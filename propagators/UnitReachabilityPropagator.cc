/* -*- Mode: C; indent-tabs-mode: t; c-basic-offset: 2; tab-width: 2 -*-  */
/*
 * UnitReachabilityPropagator.cc
 * Copyright (C) 2015 Shahab Tasharrofi <shahab.tasharrofi@gmail.com>
 *
 * graphsat is free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the
 * Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * graphsat is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "UnitReachabilityPropagator.h"

#define noURNR_PROP_DEBUG

#ifdef PROPAGATOR_DEBUG
#ifdef URNR_PROP_DEBUG
static const char *urnrPropName = "urnr";
#endif
#endif

inline int urnrFirstArc(Solver *solver, lbool targetArcValue, int graphArcCount, SATGraph::Arc *graphArcs, int reachGraphArcCount, SATGraph::Arc *reachGraphArcs)
{
	for (int i = 0; i < graphArcCount; i++)
		if (solver->value(graphArcs[i].arcLit) == targetArcValue)
			return i;

	for (int i = 0; i < reachGraphArcCount; i++)
		if (solver->value(reachGraphArcs[i].arcLit) == targetArcValue)
			return graphArcCount + i;

	return graphArcCount + reachGraphArcCount;
}

inline int urnrNextArc(Solver *solver, lbool targetArcValue, int graphArcCount, SATGraph::Arc *graphArcs, int reachGraphArcCount, SATGraph::Arc *reachGraphArcs, int curIndex)
{
	int i = curIndex + 1;
	for (; i < graphArcCount; i++)
		if (solver->value(graphArcs[i].arcLit) == targetArcValue)
			return i;

	i -= graphArcCount;
	for (; i < reachGraphArcCount; i++)
		if (solver->value(reachGraphArcs[i].arcLit) == targetArcValue)
			return graphArcCount + i;

	return graphArcCount + reachGraphArcCount;
}

void UnitReachabilityPropagator::pushNegatedPathToRoot(const OrderedDFSTree &tree, int node)
{
	assert(tree.InnerTree.hasCurrentTag(node));
	while (tree.InnerTree.getParent(node) >= 0)
	{
		urnrClause.push(~tree.InnerTree.getParentArcLit(node));
		node = tree.InnerTree.getParent(node);
	}
}

bool UnitReachabilityPropagator::propagateReachability(int source, int dest, Lit p)
{
	auto firstEnabledOutArc = [this](int node) -> int { return urnrFirstArc(SolverInstance, l_True, graph->getArcCount(node), graph->getArcs(node), reachGraph.getArcCount(node), reachGraph.getArcs(node)); };
	auto lastEnabledOutArc = [this](int node) -> int { return graph->getArcCount(node) + reachGraph.getArcCount(node); };
	auto nextEnabledOutArc = [this](int node, int curIndex) -> int { return urnrNextArc(SolverInstance, l_True, graph->getArcCount(node), graph->getArcs(node), reachGraph.getArcCount(node), reachGraph.getArcs(node), curIndex); };
	auto getEnabledOutArcByIndex = [this](int node, int curIndex) -> SATGraph::Arc* { return (curIndex < graph->getArcCount(node)) ? graph->getArcs(node) + curIndex : reachGraph.getArcs(node) + (curIndex - graph->getArcCount(node)); };

	DFSwithDummyVisitFollow<decltype(firstEnabledOutArc), decltype(lastEnabledOutArc), decltype(nextEnabledOutArc), decltype(getEnabledOutArcByIndex)>(
		dest, forwardReachableNodes, firstEnabledOutArc, lastEnabledOutArc, nextEnabledOutArc, getEnabledOutArcByIndex);

	auto firstEnabledInArc = [this](int node) -> int { return urnrFirstArc(SolverInstance, l_True, graph->getInverseArcCount(node), graph->getInverseArcs(node), reachGraph.getInverseArcCount(node), reachGraph.getInverseArcs(node)); };
	auto lastEnabledInArc = [this](int node) -> int { return graph->getInverseArcCount(node) + reachGraph.getInverseArcCount(node); };
	auto nextEnabledInArc = [this](int node, int curIndex) -> int { return urnrNextArc(SolverInstance, l_True, graph->getInverseArcCount(node), graph->getInverseArcs(node), reachGraph.getInverseArcCount(node), reachGraph.getInverseArcs(node), curIndex); };
	auto getEnabledInArcByIndex = [this](int node, int curIndex) -> SATGraph::Arc* { return (curIndex < graph->getInverseArcCount(node)) ? graph->getInverseArcs(node) + curIndex : reachGraph.getInverseArcs(node) + (curIndex - graph->getInverseArcCount(node)); };

	DFSwithDummyVisitFollow<decltype(firstEnabledInArc), decltype(lastEnabledInArc), decltype(nextEnabledInArc), decltype(getEnabledInArcByIndex)>(
		source, backwardReachableNodes, firstEnabledInArc, lastEnabledInArc, nextEnabledInArc, getEnabledInArcByIndex);

	bool lazyPropCompleted = false;

	// Check if a pair (s,t) that is asserted to be nonreachable has become reachable
	for (int nrSource = 0; nrSource < (int) nonReachabilities.size(); nrSource++)
		if (backwardReachableNodes.InnerTree.hasCurrentTag(nrSource))
			for (auto nrIt = nonReachabilities[nrSource].cbegin(); nrIt != nonReachabilities[nrSource].cend(); nrIt++)
				if ((SolverInstance->value(nrIt->second) != l_False) && forwardReachableNodes.InnerTree.hasCurrentTag(nrIt->first))
				{
					urnrClause.clearunboxed();

					urnrClause.push(~(nrIt->second));
					urnrClause.push(~p);
					pushNegatedPathToRoot(backwardReachableNodes, nrSource);
					pushNegatedPathToRoot(forwardReachableNodes, nrIt->first);

					Propagator::Effect e = addNewClause(urnrClause, lazyPropCompleted);
					switch (e)
					{
						case CONFLICT: return true;
						case DESTRUCTIVE_PROPAGATION: return false;
						case NORMAL_PROPAGATION: lazyPropCompleted = true; break;
						default: break;
					}
				}
	if (!SolverInstance->heavy_propagation)
		return false;
	if (SolverInstance->lazy_propagation && lazyPropCompleted)
		return false;

	auto firstUndefInArc = [this](int node) -> int { return urnrFirstArc(SolverInstance, l_Undef, graph->getInverseArcCount(node), graph->getInverseArcs(node), reachGraph.getInverseArcCount(node), reachGraph.getInverseArcs(node)); };
	auto lastUndefInArc = [this](int node) -> int { return graph->getInverseArcCount(node) + reachGraph.getInverseArcCount(node); };
	auto nextUndefInArc = [this](int node, int curIndex) -> int { return urnrNextArc(SolverInstance, l_Undef, graph->getInverseArcCount(node), graph->getInverseArcs(node), reachGraph.getInverseArcCount(node), reachGraph.getInverseArcs(node), curIndex); };
	auto getUndefInArcByIndex = [this](int node, int curIndex) -> SATGraph::Arc* { return (curIndex < graph->getInverseArcCount(node)) ? graph->getInverseArcs(node) + curIndex : reachGraph.getInverseArcs(node) + (curIndex - graph->getInverseArcCount(node)); };

	auto firstUndefOutArc = [this](int node) -> int { return urnrFirstArc(SolverInstance, l_Undef, graph->getArcCount(node), graph->getArcs(node), reachGraph.getArcCount(node), reachGraph.getArcs(node)); };
	auto lastUndefOutArc = [this](int node) -> int { return graph->getArcCount(node) + reachGraph.getArcCount(node); };
	auto nextUndefOutArc = [this](int node, int curIndex) -> int { return urnrNextArc(SolverInstance, l_Undef, graph->getArcCount(node), graph->getArcs(node), reachGraph.getArcCount(node), reachGraph.getArcs(node), curIndex); };
	auto getUndefOutArcByIndex = [this](int node, int curIndex) -> SATGraph::Arc* { return (curIndex < graph->getArcCount(node)) ? graph->getArcs(node) + curIndex : reachGraph.getArcs(node) + (curIndex - graph->getArcCount(node)); };

	for (int nrSource = 0; nrSource < (int) nonReachabilities.size(); nrSource++)
		for (auto nrIt = nonReachabilities[nrSource].cbegin(); nrIt != nonReachabilities[nrSource].cend(); nrIt++)
			if (SolverInstance->value(nrIt->second) == l_True)
				if (forwardReachableNodes.InnerTree.hasCurrentTag(nrIt->first) ^ backwardReachableNodes.InnerTree.hasCurrentTag(nrSource))
				{
					if (!forwardReachableNodes.InnerTree.hasCurrentTag(nrIt->first))
					{
						for (int i = firstUndefInArc(nrIt->first); i != lastUndefInArc(nrIt->first); i = nextUndefInArc(nrIt->first, i))
							if (forwardReachableNodes.InnerTree.hasCurrentTag(getUndefInArcByIndex(nrIt->first, i)->succNode))
							{
								Lit undefArcLit = getUndefInArcByIndex(nrIt->first, i)->arcLit;

								urnrClause.clearunboxed();
								urnrClause.push(~undefArcLit);
								urnrClause.push(~p);
								urnrClause.push(~nrIt->second);
								pushNegatedPathToRoot(backwardReachableNodes, nrSource);
								pushNegatedPathToRoot(forwardReachableNodes, getUndefInArcByIndex(nrIt->first, i)->succNode);

								Propagator::Effect e = addNewClause(urnrClause, false);
								if (e == CONFLICT)
									return true;
								else if ((e == DESTRUCTIVE_PROPAGATION) || ((e == NORMAL_PROPAGATION) && SolverInstance->lazy_propagation))
									return false;
							}
					}

					if (!backwardReachableNodes.InnerTree.hasCurrentTag(nrSource))
					{
						for (int i = firstUndefOutArc(nrSource); i != lastUndefOutArc(nrSource); i = nextUndefOutArc(nrSource, i))
							if (backwardReachableNodes.InnerTree.hasCurrentTag(getUndefOutArcByIndex(nrSource, i)->succNode))
							{
								Lit undefArcLit = getUndefOutArcByIndex(nrSource, i)->arcLit;

								urnrClause.clearunboxed();
								urnrClause.push(~undefArcLit);
								urnrClause.push(~p);
								urnrClause.push(~nrIt->second);
								pushNegatedPathToRoot(backwardReachableNodes, getUndefOutArcByIndex(nrSource, i)->succNode);
								pushNegatedPathToRoot(forwardReachableNodes, nrIt->first);

								Propagator::Effect e = addNewClause(urnrClause, false);
								if (e == CONFLICT)
									return true;
								else if ((e == DESTRUCTIVE_PROPAGATION) || ((e == NORMAL_PROPAGATION) && SolverInstance->lazy_propagation))
									return false;
							}
					}
				}

	return false;
}

bool UnitReachabilityPropagator::propagateNonReachability(int source, int dest, Lit p)
{
	auto firstEnabledOutArc = [this](int node) -> int { return urnrFirstArc(SolverInstance, l_True, graph->getArcCount(node), graph->getArcs(node), reachGraph.getArcCount(node), reachGraph.getArcs(node)); };
	auto lastEnabledOutArc = [this](int node) -> int { return graph->getArcCount(node) + reachGraph.getArcCount(node); };
	auto nextEnabledOutArc = [this](int node, int curIndex) -> int { return urnrNextArc(SolverInstance, l_True, graph->getArcCount(node), graph->getArcs(node), reachGraph.getArcCount(node), reachGraph.getArcs(node), curIndex); };
	auto getEnabledOutArcByIndex = [this](int node, int curIndex) -> SATGraph::Arc* { return (curIndex < graph->getArcCount(node)) ? graph->getArcs(node) + curIndex : reachGraph.getArcs(node) + (curIndex - graph->getArcCount(node)); };

	DFSwithDummyVisitFollow<decltype(firstEnabledOutArc), decltype(lastEnabledOutArc), decltype(nextEnabledOutArc), decltype(getEnabledOutArcByIndex)>(
		source, forwardReachableNodes, firstEnabledOutArc, lastEnabledOutArc, nextEnabledOutArc, getEnabledOutArcByIndex);

	if (forwardReachableNodes.InnerTree.hasCurrentTag(dest))
	{
		urnrClause.clearunboxed();

		urnrClause.push(~p);
		pushNegatedPathToRoot(forwardReachableNodes, dest);

		Propagator::Effect e = addNewClause(urnrClause, false);
		return (e == CONFLICT);
	}

	if (!SolverInstance->heavy_propagation)
		return false;

	auto firstEnabledInArc = [this](int node) -> int { return urnrFirstArc(SolverInstance, l_True, graph->getInverseArcCount(node), graph->getInverseArcs(node), reachGraph.getInverseArcCount(node), reachGraph.getInverseArcs(node)); };
	auto lastEnabledInArc = [this](int node) -> int { return graph->getInverseArcCount(node) + reachGraph.getInverseArcCount(node); };
	auto nextEnabledInArc = [this](int node, int curIndex) -> int { return urnrNextArc(SolverInstance, l_True, graph->getInverseArcCount(node), graph->getInverseArcs(node), reachGraph.getInverseArcCount(node), reachGraph.getInverseArcs(node), curIndex); };
	auto getEnabledInArcByIndex = [this](int node, int curIndex) -> SATGraph::Arc* { return (curIndex < graph->getInverseArcCount(node)) ? graph->getInverseArcs(node) + curIndex : reachGraph.getInverseArcs(node) + (curIndex - graph->getInverseArcCount(node)); };

	DFSwithDummyVisitFollow<decltype(firstEnabledInArc), decltype(lastEnabledInArc), decltype(nextEnabledInArc), decltype(getEnabledInArcByIndex)>(
		dest, backwardReachableNodes, firstEnabledInArc, lastEnabledInArc, nextEnabledInArc, getEnabledInArcByIndex);

	auto firstUndefOutArc = [this](int node) -> int { return urnrFirstArc(SolverInstance, l_Undef, graph->getArcCount(node), graph->getArcs(node), reachGraph.getArcCount(node), reachGraph.getArcs(node)); };
	auto lastUndefOutArc = [this](int node) -> int { return graph->getArcCount(node) + reachGraph.getArcCount(node); };
	auto nextUndefOutArc = [this](int node, int curIndex) -> int { return urnrNextArc(SolverInstance, l_Undef, graph->getArcCount(node), graph->getArcs(node), reachGraph.getArcCount(node), reachGraph.getArcs(node), curIndex); };
	auto getUndefOutArcByIndex = [this](int node, int curIndex) -> SATGraph::Arc* { return (curIndex < graph->getArcCount(node)) ? graph->getArcs(node) + curIndex : reachGraph.getArcs(node) + (curIndex - graph->getArcCount(node)); };

	for (int u = 0; u < graph->nodeCount; u++)
		if (forwardReachableNodes.InnerTree.hasCurrentTag(u))
			for (int i = firstUndefOutArc(u); i != lastUndefOutArc(u); i = nextUndefOutArc(u, i))
				if (backwardReachableNodes.InnerTree.hasCurrentTag(getUndefOutArcByIndex(u, i)->succNode))
				{
					Lit undefArcLit = getUndefOutArcByIndex(u, i)->arcLit;

					urnrClause.clearunboxed();
					urnrClause.push(~undefArcLit);
					urnrClause.push(~p);
					pushNegatedPathToRoot(backwardReachableNodes, getUndefOutArcByIndex(u, i)->succNode);
					pushNegatedPathToRoot(forwardReachableNodes, u);

					Propagator::Effect e = addNewClause(urnrClause, false);
					if (e == CONFLICT)
						return true;
					else if ((e == DESTRUCTIVE_PROPAGATION) || ((e == NORMAL_PROPAGATION) && SolverInstance->lazy_propagation))
						return false;
				}

	return false;
}

UnitReachabilityPropagator::UnitReachabilityPropagator(Solver *solver, SATGraph *graph, const unordered_map<int, unordered_map<int, Lit> > &reachabilities, const unordered_map<int, unordered_map<int, Lit> > &nonReachabilities) :
	Propagator(solver),
	reachabilityPairsByLiteral(solver->nVars() * 2 + 3),
	nonReachabilityPairsByLiteral(solver->nVars() * 2 + 3),
	forwardReachableNodes(graph->nodeCount + 1),
	backwardReachableNodes(graph->nodeCount + 1)
{
#ifdef PROPAGATOR_DEBUG
#ifdef URNR_PROP_DEBUG
	debuggingEnabled = true;
	propagatorName = urnrPropName;
#endif
#endif
	this->graph = graph;

	for (int i = 0; i < graph->nodeCount; i++)
		this->reachabilities.push_back(vector< pair<int, Lit> >());
	for (auto sourceIt = reachabilities.cbegin(); sourceIt != reachabilities.cend(); sourceIt++)
		for (auto targetIt = sourceIt->second.cbegin(); targetIt != sourceIt->second.cend(); targetIt++)
		{
			this->reachabilities[sourceIt->first].push_back(*targetIt);
			reachabilityPairsByLiteral.insert(targetIt->second.x, pair<int, int>(sourceIt->first, targetIt->first));
		}

	for (int i = 0; i <= graph->nodeCount; i++)
		this->nonReachabilities.push_back(vector< pair<int, Lit> >());
	for (auto sourceIt = nonReachabilities.cbegin(); sourceIt != nonReachabilities.cend(); sourceIt++)
		for (auto targetIt = sourceIt->second.cbegin(); targetIt != sourceIt->second.cend(); targetIt++)
		{
			this->nonReachabilities[sourceIt->first].push_back(*targetIt);
			nonReachabilityPairsByLiteral.insert(targetIt->second.x, pair<int, int>(sourceIt->first, targetIt->first));
		}

	reachGraph.createGraph(solver->nVars());
	reachGraph.initGraph(graph->nodeCount);
	for (int node = 0; node < (int) this->reachabilities.size(); node++)
		reachGraph.createNode(node, this->reachabilities[node].size());
	for (int node = (int) this->reachabilities.size(); node < graph->nodeCount; node++)
		reachGraph.createNode(node, 0);
	for (int node = 0; node < (int) this->reachabilities.size(); node++)
		for (auto it = this->reachabilities[node].cbegin(); it != this->reachabilities[node].cend(); it++)
			reachGraph.addArc(it->second, node, it->first);
	reachGraph.createInverseArcs();
}

bool UnitReachabilityPropagator::initialize(void)
{
	return true;
}

bool UnitReachabilityPropagator::propagate(Lit p)
{
	if (reachabilityPairsByLiteral.hasKey(p.x))
	{
		pair<int, int> reachPair = reachabilityPairsByLiteral.valueOf(p.x);
		if (propagateReachability(reachPair.first, reachPair.second, p))
			return true;
	}

	if (nonReachabilityPairsByLiteral.hasKey(p.x))
	{
		pair<int, int> nonReachPair = nonReachabilityPairsByLiteral.valueOf(p.x);
		if (propagateNonReachability(nonReachPair.first, nonReachPair.second, p))
			return true;
	}

	if (graph->isGraphArc(var(p)) && !sign(p))
		if (propagateReachability(graph->sourceNode(p), graph->targetNode(p), p))
			return true;

	return false;
}

const vec<Lit> &UnitReachabilityPropagator::explain()
{
	assert(false);
}

bool UnitReachabilityPropagator::isTheoryVar(Var v)
{
	Lit p = mkLit(v, false);
	Lit negP = ~p;
	if (reachabilityPairsByLiteral.hasKey(p.x) || reachabilityPairsByLiteral.hasKey(negP.x))
		return true;
	if (nonReachabilityPairsByLiteral.hasKey(p.x) || nonReachabilityPairsByLiteral.hasKey(negP.x))
		return true;
	return graph->isGraphArc(v);
}

Propagator *UnitReachabilityPropagator::copy(Solver *S)
{
	unordered_map<int, unordered_map<int, Lit> > reaches;
	unordered_map<int, unordered_map<int, Lit> > nonReaches;

	for (size_t i = 0; i < reachabilities.size(); i++)
		if (reachabilities[i].size() > 0)
		{
			reaches[i] = unordered_map<int, Lit>();
			for (auto it = reachabilities[i].cbegin(); it != reachabilities[i].cend(); it++)
				reaches[i][it->first] = it->second;
		}

	for (size_t i = 0; i < nonReachabilities.size(); i++)
		if (nonReachabilities[i].size() > 0)
		{
			nonReaches[i] = unordered_map<int, Lit>();
			for (auto it = nonReachabilities[i].cbegin(); it != nonReachabilities[i].cend(); it++)
				nonReaches[i][it->first] = it->second;
		}

	return new UnitReachabilityPropagator(S, graph, reaches, nonReaches);
}

