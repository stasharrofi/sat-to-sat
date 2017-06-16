/*
 * GeneralizedNonreachabilityPropagator.cc
 * Copyright (C) 2015 Shahab <shahab.tasharrofi@aalto.fi>
 *
 * graph-minisat is free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the
 * Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * graph-minisat is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "GeneralizedNonreachabilityPropagator.h"

#define noGENERALIZED_NONREACH_DEBUG

#ifdef GENERALIZED_NONREACH_DEBUG
#define noDEEP_GENERALIZED_NONREACH_DEBUG
#endif

#ifdef PROPAGATOR_DEBUG
#ifdef GENERALIZED_NONREACH_DEBUG
static const char *genNonReachPropName = "gen-nreach";
#endif
#endif

GeneralizedNonreachabilityPropagator::GeneralizedNonreachabilityPropagator(Solver *S, int nOfVars, SATGraph *G, const vector< tuple<int, int, Lit> > &NonreachablePairs)
	: Propagator(S),
		sourceNodeFromLit(nOfVars * 2 + 3),
		destNodeFromLit(nOfVars * 2 + 3)
{
#ifdef PROPAGATOR_DEBUG
#ifdef GENERALIZED_NONREACH_DEBUG
	debuggingEnabled = true;
	propagatorName = genNonReachPropName;
#endif
#endif
	Graph = G;

	for (int i = 0; i <= G->nodeCount; i++)
	{
		nodeToFRIndex.push_back(-1);
		nodeToBRIndex.push_back(-1);
	}

	for (auto it = NonreachablePairs.cbegin(); it != NonreachablePairs.cend(); it++)
	{
		int sourceNode = std::get<0>(*it), destNode = std::get<1>(*it);
		int litNumber = std::get<2>(*it).x;

		sourceNodeFromLit.insert(litNumber, sourceNode);
		destNodeFromLit.insert(litNumber, destNode);
		litFromNodePair[sourceNode][destNode] = std::get<2>(*it);

		if (nodeToFRIndex[sourceNode] < 0)
		{
			nodeToFRIndex[sourceNode] = forwardDFSTrees.size();
			forwardDFSTrees.push_back(OrderedDFSTree(Graph->nodeCount + 1));
		}

		if (nodeToBRIndex[destNode] < 0)
		{
			nodeToBRIndex[destNode] = backwardDFSTrees.size();
			backwardDFSTrees.push_back(OrderedDFSTree(Graph->nodeCount + 1));
		}
	}

	initialized = false;
}

bool GeneralizedNonreachabilityPropagator::initialize(void)
{
#ifdef GENERALIZED_REACH_DEBUG
	printf("generalized non-reachability: initializing\n");
#endif
	return true;
}

bool GeneralizedNonreachabilityPropagator::isTheoryVar(Var v)
{
  return Graph->isGraphArc(v) ||
				 sourceNodeFromLit.hasKey(mkLit(v).x) ||
				 sourceNodeFromLit.hasKey(mkLit(v, true).x);
}

inline int genNonreachFirstEnabledOutArcIndex(SATGraph *G, Solver *S, int node)
{
	SATGraph::Arc *arcs = G->getArcs(node);

	for (int i = 0; i < G->getArcCount(node); i++)
		if (S->value(arcs[i].arcLit) == l_True)
			return i;

	return G->getArcCount(node);
}

inline int genNonreachNextEnabledOutArcIndex(SATGraph *G, Solver *S, int node, int curIndex)
{
	SATGraph::Arc *arcs = G->getArcs(node);

	for (int i = curIndex + 1; i < G->getArcCount(node); i++)
		if (S->value(arcs[i].arcLit) == l_True)
			return i;

	return G->getArcCount(node);
}

inline int genNonreachFirstInModelOutArcIndex(SATGraph *G, Solver *S, int node)
{
	SATGraph::Arc *arcs = G->getArcs(node);

	for (int i = 0; i < G->getArcCount(node); i++)
		if (S->modelValue(arcs[i].arcLit) == l_True)
			return i;

	return G->getArcCount(node);
}

inline int genNonreachNextInModelOutArcIndex(SATGraph *G, Solver *S, int node, int curIndex)
{
	SATGraph::Arc *arcs = G->getArcs(node);

	for (int i = curIndex + 1; i < G->getArcCount(node); i++)
		if (S->modelValue(arcs[i].arcLit) == l_True)
			return i;

	return G->getArcCount(node);
}

inline int genNonreachFirstEnabledInArcIndex(SATGraph *G, Solver *S, int node)
{
	SATGraph::Arc *arcs = G->getInverseArcs(node);

	for (int i = 0; i < G->getInverseArcCount(node); i++)
		if (S->value(arcs[i].arcLit) == l_True)
			return i;

	return G->getInverseArcCount(node);
}

inline int genNonreachNextEnabledInArcIndex(SATGraph *G, Solver *S, int node, int curIndex)
{
	SATGraph::Arc *arcs = G->getInverseArcs(node);

	for (int i = curIndex + 1; i < G->getInverseArcCount(node); i++)
		if (S->value(arcs[i].arcLit) == l_True)
			return i;

	return G->getInverseArcCount(node);
}

void GeneralizedNonreachabilityPropagator::initializeReachabilities()
{
	auto fstOut = [this](int node) -> int { return genNonreachFirstEnabledOutArcIndex(Graph, SolverInstance, node); };
	auto lstOut = [this](int node) -> int { return Graph->getArcCount(node); };
	auto nextOut = [this](int node, int curIndex) -> int { return genNonreachNextEnabledOutArcIndex(Graph, SolverInstance, node, curIndex); };
	auto outArcByIdx = [this](int node, int curIndex) -> SATGraph::Arc* { return Graph->getArcs(node) + curIndex; };

	for (size_t i = 0; i < nodeToFRIndex.size(); i++)
	{
		int index = nodeToFRIndex[i];
		if (index >= 0)
			DFSwithDummyVisitFollow<decltype(fstOut), decltype(lstOut), decltype(nextOut), decltype(outArcByIdx)>(
				i, forwardDFSTrees[index], fstOut, lstOut, nextOut, outArcByIdx);
	}

	auto fstIn = [this](int node) -> int { return genNonreachFirstEnabledInArcIndex(Graph, SolverInstance, node); };
	auto lstIn = [this](int node) -> int { return Graph->getInverseArcCount(node); };
	auto nextIn = [this](int node, int curIndex) -> int { return genNonreachNextEnabledInArcIndex(Graph, SolverInstance, node, curIndex); };
	auto inArcByIdx = [this](int node, int curIndex) -> SATGraph::Arc* { return Graph->getInverseArcs(node) + curIndex; };

	for (size_t i = 0; i < nodeToBRIndex.size(); i++)
	{
		int index = nodeToBRIndex[i];
		if (index >= 0)
			DFSwithDummyVisitFollow<decltype(fstIn), decltype(lstIn), decltype(nextIn), decltype(inArcByIdx)>(
				i, backwardDFSTrees[index], fstIn, lstIn, nextIn, inArcByIdx);
	}

	initialized = true;
}

void GeneralizedNonreachabilityPropagator::extendReachabilities(int sourceNode, int targetNode, Lit arcLit)
{
	auto fstOut = [this](int node) -> int { return genNonreachFirstEnabledOutArcIndex(Graph, SolverInstance, node); };
	auto lstOut = [this](int node) -> int { return Graph->getArcCount(node); };
	auto nextOut = [this](int node, int curIndex) -> int { return genNonreachNextEnabledOutArcIndex(Graph, SolverInstance, node, curIndex); };
	auto outArcByIdx = [this](int node, int curIndex) -> SATGraph::Arc* { return Graph->getArcs(node) + curIndex; };

	for (size_t i = 0; i < nodeToFRIndex.size(); i++)
	{
		int index = nodeToFRIndex[i];
		if ((index >= 0) && forwardDFSTrees[index].InnerTree.hasCurrentTag(sourceNode) &&
		    !forwardDFSTrees[index].InnerTree.hasCurrentTag(targetNode))
			IncrementalDFSwithDummyVisitFollow<decltype(fstOut), decltype(lstOut), decltype(nextOut), decltype(outArcByIdx)>(
				targetNode, sourceNode, arcLit, forwardDFSTrees[index], fstOut, lstOut, nextOut, outArcByIdx);
	}

	if (SolverInstance->heavy_propagation == false)
		return;

	auto fstIn = [this](int node) -> int { return genNonreachFirstEnabledInArcIndex(Graph, SolverInstance, node); };
	auto lstIn = [this](int node) -> int { return Graph->getInverseArcCount(node); };
	auto nextIn = [this](int node, int curIndex) -> int { return genNonreachNextEnabledInArcIndex(Graph, SolverInstance, node, curIndex); };
	auto inArcByIdx = [this](int node, int curIndex) -> SATGraph::Arc* { return Graph->getInverseArcs(node) + curIndex; };

	for (size_t i = 0; i < nodeToBRIndex.size(); i++)
	{
		int index = nodeToBRIndex[i];
		if ((index >= 0) && backwardDFSTrees[index].InnerTree.hasCurrentTag(targetNode) &&
		    !backwardDFSTrees[index].InnerTree.hasCurrentTag(sourceNode))
			IncrementalDFSwithDummyVisitFollow<decltype(fstIn), decltype(lstIn), decltype(nextIn), decltype(inArcByIdx)>(
				sourceNode, targetNode, arcLit, backwardDFSTrees[index], fstIn, lstIn, nextIn, inArcByIdx);
	}
}

/*________________________________________________________________________
|
| propagateNonreachability
|
| Description:
|   When an arc in the graph is set to TRUE or when the non-reachability of
|   node t from node s is asserted, infer arcs that must hold for two nodes
|   to remain separate.
|
|___________________________________________________________________________*/

bool GeneralizedNonreachabilityPropagator::propagate(Minisat::Lit p)
{
#ifdef DEEP_GENERALIZED_NONREACH_DEBUG
	printf("generalized nonreachability: propagating %i\n", ConvertLiteralToInt(p));
#endif
	// In order for p to be an important literal to this theory, it either
	// has to assert that non-reachability of two nodes or it should enable
	// an arc.
	if (!(sourceNodeFromLit.hasKey(p.x) || (!sign(p) && Graph->isGraphArc(Minisat::var(p)))))
		return false;

	if (!initialized)
		initializeReachabilities();
	else if (Graph->isGraphArc(Minisat::var(p)) && (Graph->label(p) == p))
		extendReachabilities(Graph->sourceNode(p), Graph->targetNode(p), p);

	bool lazyPropCompleted = false;
	for (auto it = litFromNodePair.cbegin(); it != litFromNodePair.cend(); it++)
	{
		int index = nodeToFRIndex[it->first];
		for (auto jt = it->second.cbegin(); jt != it->second.cend(); jt++)
		{
			if (SolverInstance->lazy_propagation && lazyPropCompleted && (SolverInstance->value(jt->second) != l_True))
				continue;
			if (forwardDFSTrees[index].InnerTree.hasCurrentTag(jt->first) && (SolverInstance->value(jt->second) != l_False))
			{
				nonreachClause.clear();
				nonreachClause.push(~(jt->second));

				int currentNode = jt->first;
				while (currentNode != it->first)
				{
					nonreachClause.push(~forwardDFSTrees[index].InnerTree.getParentArcLit(currentNode));
					currentNode = forwardDFSTrees[index].InnerTree.getParent(currentNode);
				}

				Propagator::Effect e = addNewClause(nonreachClause, lazyPropCompleted);
				switch (e)
				{
					case CONFLICT: return true;
					case DESTRUCTIVE_PROPAGATION: return false;
					case NORMAL_PROPAGATION: lazyPropCompleted = true; break;
					default: break;
				}
			}
		}
	}

	if (SolverInstance->heavy_propagation == false)
		return false;
	if (SolverInstance->lazy_propagation && lazyPropCompleted)
		return false;

	for (int i = 0; i < Graph->nodeCount; i++)
	{
		SATGraph::Arc *outArcs = Graph->getArcs(i);
		for (int j = 0; j < Graph->getArcCount(i); j++, outArcs++)
			if (SolverInstance->value(outArcs->arcLit) == l_Undef)
			{ // we have found an arc u --> v that is unaasigned, should decide if it needs to be propagated to false
				bool propagated = false;
				for (auto it = litFromNodePair.cbegin(); it != litFromNodePair.cend(); it++)
				{ // we iterate over all non-reachable pairs (s,t)
					int fIndex = nodeToFRIndex[it->first];
					if (forwardDFSTrees[fIndex].InnerTree.hasCurrentTag(i) && !forwardDFSTrees[fIndex].InnerTree.hasCurrentTag(outArcs->succNode))
					{ // if s can reach u but cannot reach v the arc (u,v) might be important
						for (auto jt = it->second.cbegin(); jt != it->second.cend(); jt++)
						{
							int bIndex = nodeToBRIndex[jt->first];
							if (backwardDFSTrees[bIndex].InnerTree.hasCurrentTag(outArcs->succNode) &&
							    (SolverInstance->value(jt->second) == l_True))
							{ // if t can reach v in backwards then arc (u,v) should be disabled
								nonreachClause.clear();
								nonreachClause.push(~outArcs->arcLit);
								nonreachClause.push(~(jt->second));

								int currentNode = i;
								while (currentNode != it->first)
								{
									nonreachClause.push(~forwardDFSTrees[fIndex].InnerTree.getParentArcLit(currentNode));
									currentNode = forwardDFSTrees[fIndex].InnerTree.getParent(currentNode);
								}

								currentNode = outArcs->succNode;
								while (currentNode != jt->first)
								{
									nonreachClause.push(~backwardDFSTrees[bIndex].InnerTree.getParentArcLit(currentNode));
									currentNode = backwardDFSTrees[bIndex].InnerTree.getParent(currentNode);
								}

								Propagator::Effect e = addNewClause(nonreachClause, false);
								if (e == CONFLICT)
									return true;
								else if (SolverInstance->lazy_propagation || (e == DESTRUCTIVE_PROPAGATION))
									return false;

								propagated = true;
								break;
							}
						}
						if (propagated)
							break;
					}
				}
			}
	}

	return false;
}

void GeneralizedNonreachabilityPropagator::cancelUntil(int level)
{
	initialized = false;
}

const vec<Lit> &GeneralizedNonreachabilityPropagator::explain()
{
	auto fstOutInModel = [this](int node) -> int { return genNonreachFirstInModelOutArcIndex(Graph, SolverInstance, node); };
	auto lstOut = [this](int node) -> int { return Graph->getArcCount(node); };
	auto nextOutInModel = [this](int node, int curIndex) -> int { return genNonreachNextInModelOutArcIndex(Graph, SolverInstance, node, curIndex); };
	auto outArcByIdx = [this](int node, int curIndex) -> SATGraph::Arc* { return Graph->getArcs(node) + curIndex; };

	nonreachClause.clear();
	for (auto it = litFromNodePair.cbegin(); it != litFromNodePair.cend(); it++)
	{
		int fIndex = nodeToFRIndex[it->first];
		DFSwithDummyVisitFollow<decltype(fstOutInModel), decltype(lstOut), decltype(nextOutInModel), decltype(outArcByIdx)>(
			it->first, forwardDFSTrees[fIndex], fstOutInModel, lstOut, nextOutInModel, outArcByIdx);

		for (auto jt = it->second.cbegin(); jt != it->second.cend(); jt++)
			if (SolverInstance->modelValue(jt->second) == l_False)
				nonreachClause.push(~(jt->second));
	}

	for (int i = 0; i < Graph->nodeCount; i++)
	{
		SATGraph::Arc *outArcs = Graph->getArcs(i);
		for (int j = 0; j < Graph->getArcCount(i); j++, outArcs++)
		{
			bool test = false;
			for (auto it = litFromNodePair.cbegin(); it != litFromNodePair.cend(); it++)
			{
				int index = nodeToFRIndex[it->first];
				if (forwardDFSTrees[index].InnerTree.hasCurrentTag(i) && !forwardDFSTrees[index].InnerTree.hasCurrentTag(outArcs->succNode))
					for (auto jt = it->second.cbegin(); jt != it->second.cend(); jt++)
						if ((SolverInstance->modelValue(jt->second) == l_True) && Graph->isBackwardReachable(jt->first, outArcs->succNode))
						{
							test = true;
							break;
						}

				if (test)
					break;
			}

			if (test)
				nonreachClause.push(~outArcs->arcLit);
		}
	}

	return nonreachClause;
}

Propagator *GeneralizedNonreachabilityPropagator::copy(Solver *S)
{
	vector< tuple<int, int, Lit> > NonreachablePairs;
	for (auto it = litFromNodePair.cbegin(); it != litFromNodePair.cend(); it++)
		for (auto jt = it->second.cbegin(); jt != it->second.cend(); jt++)
			NonreachablePairs.push_back(tuple<int, int, Lit>(it->first, jt->first, jt->second));

	return new GeneralizedNonreachabilityPropagator(S, S->nVars(), Graph, NonreachablePairs);
}


