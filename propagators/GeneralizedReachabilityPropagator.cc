/* -*- Mode: C; indent-tabs-mode: t; c-basic-offset: 2; tab-width: 2 -*-  */
/*
 * GeneralizedReachabilityPropagator.cc
 * Copyright (C) 2015 Shahab Tasharrofi <>
 *
 * minisatAcycReach is free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the
 * Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * minisatAcycReach is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "GeneralizedReachabilityPropagator.h"

#define noGENERALIZED_REACH_DEBUG

#ifdef GENERALIZED_REACH_DEBUG
#define noDEEP_GENERALIZED_REACH_DEBUG
#endif

#ifdef PROPAGATOR_DEBUG
#ifdef GENERALIZED_REACH_DEBUG
static const char *genReachPropName = "gen-reach";
#endif
#endif

GeneralizedReachabilityPropagator::GeneralizedReachabilityPropagator(Solver *S, int nOfVars, SATGraph *G, int SourceNode, const unordered_map<int, Lit> &DestNodes)
	: Propagator(S),
		DestinationsMap(G->nodeCount + 1),
		DestinationLits(2 * nOfVars + 3),
		Tree(G->nodeCount),
		TreeEdgeLits(2 * nOfVars + 3),
		BridgeWatchedArcLits(2 * nOfVars + 3)
{
#ifdef PROPAGATOR_DEBUG
#ifdef GENERALIZED_REACH_DEBUG
	debuggingEnabled = true;
	propagatorName = genReachPropName;
#endif
#endif
	Graph = G;
	Source = SourceNode;

	for (auto it = DestNodes.cbegin(); it != DestNodes.cend(); it++)
	{
		DestinationNodes.push_back(it->first);
		DestinationLits.insert(it->second.x);
		DestinationsMap.insert(it->first, it->second);
	}

	Initialized = false;
}

bool GeneralizedReachabilityPropagator::initialize(void)
{
#ifdef GENERALIZED_REACH_DEBUG
	printf("generalized reachability: initializing\n");
#endif
	return performPropagations(true, true);
}

bool GeneralizedReachabilityPropagator::isTheoryVar(Var v)
{
  return Graph->isGraphArc(v) || DestinationLits.hasMember(mkLit(v).x) || DestinationLits.hasMember((~mkLit(v)).x);
}

inline int genReachFirstPossibleOutArcIndex(SATGraph *G, Solver *S, int node)
{
	SATGraph::Arc *arcs = G->getArcs(node);

	for (int i = 0; i < G->getArcCount(node); i++)
		if (S->value(arcs[i].arcLit) != l_False)
			return i;

	return G->getArcCount(node);
}

inline int genReachNextPossibleOutArcIndex(SATGraph *G, Solver *S, int node, int curIndex)
{
	SATGraph::Arc *arcs = G->getArcs(node);

	for (int i = curIndex + 1; i < G->getArcCount(node); i++)
		if (S->value(arcs[i].arcLit) != l_False)
			return i;

	return G->getArcCount(node);
}

inline int genReachFirstInModelOutArcIndex(SATGraph *G, Solver *S, int node)
{
	SATGraph::Arc *arcs = G->getArcs(node);

	for (int i = 0; i < G->getArcCount(node); i++)
		if (S->modelValue(arcs[i].arcLit) == l_True)
			return i;

	return G->getArcCount(node);
}

inline int genReachNextInModelOutArcIndex(SATGraph *G, Solver *S, int node, int curIndex)
{
	SATGraph::Arc *arcs = G->getArcs(node);

	for (int i = curIndex + 1; i < G->getArcCount(node); i++)
		if (S->modelValue(arcs[i].arcLit) == l_True)
			return i;

	return G->getArcCount(node);
}

inline int genReachFirstPossibleInArcIndex(SATGraph *G, Solver *S, int node)
{
	SATGraph::Arc *arcs = G->getInverseArcs(node);

	for (int i = 0; i < G->getInverseArcCount(node); i++)
		if (S->value(arcs[i].arcLit) != l_False)
			return i;

	return G->getInverseArcCount(node);
}

inline int genReachNextPossibleInArcIndex(SATGraph *G, Solver *S, int node, int curIndex)
{
	SATGraph::Arc *arcs = G->getInverseArcs(node);

	for (int i = curIndex + 1; i < G->getInverseArcCount(node); i++)
		if (S->value(arcs[i].arcLit) != l_False)
			return i;

	return G->getInverseArcCount(node);
}

bool GeneralizedReachabilityPropagator::performPropagations(bool findNewDFSTree, bool checkNonreachability)
{
	bool lazyPropCompleted = false;
	if (!Initialized || checkNonreachability)
	{
		if (!Initialized || findNewDFSTree)
		{
			auto fstOut = [this](int node) -> int { return genReachFirstPossibleOutArcIndex(Graph, SolverInstance, node); };
			auto lstOut = [this](int node) -> int { return Graph->getArcCount(node); };
			auto nextOut = [this](int node, int curIndex) -> int { return genReachNextPossibleOutArcIndex(Graph, SolverInstance, node, curIndex); };
			auto outArcByIdx = [this](int node, int curIndex) -> SATGraph::Arc* { return Graph->getArcs(node) + curIndex; };

			DFSwithDummyVisitFollow<decltype(fstOut), decltype(lstOut), decltype(nextOut), decltype(outArcByIdx)>(
				Source, Tree.DFSTree, fstOut, lstOut, nextOut, outArcByIdx);
		}

		for (auto it = DestinationNodes.cbegin(); it != DestinationNodes.cend(); ++it)
		{
			int destNode = (*it);
			if (!Tree.DFSTree.InnerTree.hasCurrentTag(destNode))
			{
				Lit destLit = DestinationsMap.valueOf(destNode);
				if (SolverInstance->lazy_propagation && lazyPropCompleted && SolverInstance->value(destLit) != l_True)
					continue;

				if (SolverInstance->value(destLit) != l_False)
				{
					reach_clause.clearunboxed();
					// Either the reachability of "it->first" (i.e., "it->second") should not be asserted
					reach_clause.push(~destLit);
					// Or there should exist a path between "Source" node and "it->first"
					for (int i = 0; i < Tree.DFSTree.treeSize; i++)
					{
						int curNode = Tree.DFSTree.nodeOrderings[i];
						auto arcList = Graph->getArcs(curNode);
						for (int j = 0; j < Graph->getArcCount(curNode); j++)
							if (!Tree.DFSTree.InnerTree.hasCurrentTag(arcList[j].succNode))
								if (Graph->isBackwardReachable(destNode, arcList[j].succNode))
									reach_clause.push(arcList[j].arcLit);
					}

#ifdef GENERALIZED_REACH_DEBUG
					if (SolverInstance->value(destLit) == l_True)
						printf("generalized reachability: conflict clause found: "); // It's a conflict if "it->first" is asserted to be reachable
					else
						printf("generalized reachability: propagating non-reachability of node %d: ", destNode); // It's a learnt clause if "it->first" otherwise

					for (int i = 0; i < reach_clause.size(); i++)
						printf("%i ", ConvertLiteralToInt(reach_clause[i]));
					printf("\n");
#endif
					Propagator::Effect e = addNewClause(reach_clause, lazyPropCompleted);
					switch (e)
					{
						case CONFLICT: return false;
						case DESTRUCTIVE_PROPAGATION: return true;
						case NORMAL_PROPAGATION: lazyPropCompleted = true; break;
						default: break;
					}
				}
			}
		}

		auto possibleDests = [this](int node) -> bool
			{
				return DestinationsMap.hasKey(node) ? (SolverInstance->value(DestinationsMap.valueOf(node)) != l_False) : false;
			};
		findUsefulSubtrees<decltype(possibleDests)>(Tree.DFSTree, possibleDests); 

		TreeEdgeLits.clear();
		for (int i = 1; i < Tree.DFSTree.treeSize; i++)
			if (Tree.DFSTree.subtreeUsefulnessWitness[i] >= 0)
				TreeEdgeLits.insert(Tree.DFSTree.InnerTree.getParentArcLit(Tree.DFSTree.nodeOrderings[i]).x);
	}

	if ((!SolverInstance->heavy_propagation) || (SolverInstance->lazy_propagation && lazyPropCompleted))
	{
		Initialized = true;
		return true;
	}

	BridgeWatchedArcLits.clear();
	for (int i = 1; i < Tree.DFSTree.treeSize; i++)
	{
		Lit parentArcLit = Tree.DFSTree.InnerTree.getParentArcLit(Tree.DFSTree.nodeOrderings[i]);
#ifdef DEEP_GENERALIZED_REACH_DEBUG
		printf("generalized reachability: arc %d (part of DFS tree) is being watched for bridge propagation.\n", ConvertLiteralToInt(parentArcLit));
#endif
		if (SolverInstance->value(parentArcLit) == l_Undef)
			BridgeWatchedArcLits.insert(parentArcLit.x);
	}

	auto fstIn = [this](int node) -> int { return genReachFirstPossibleInArcIndex(Graph, SolverInstance, node); };
	auto lstIn = [this](int node) -> int { return Graph->getInverseArcCount(node); };
	auto nextIn = [this](int node, int curIndex) -> int { return genReachNextPossibleInArcIndex(Graph, SolverInstance, node, curIndex); };
	auto inArcByIdx = [this](int node, int curIndex) -> SATGraph::Arc* { return Graph->getInverseArcs(node) + curIndex; };

	findBridges<decltype(fstIn), decltype(lstIn), decltype(nextIn), decltype(inArcByIdx)>(Tree, fstIn, lstIn, nextIn, inArcByIdx);

	auto enabledDests = [this](int node) -> bool
	{
		return DestinationsMap.hasKey(node) ? (SolverInstance->value(DestinationsMap.valueOf(node)) == l_True) : false;
	};

	findUsefulSubtrees<decltype(enabledDests)>(Tree.DFSTree, enabledDests);

	for (int i = 1; i < Tree.DFSTree.treeSize; i++)
		if (Tree.nonBridgeWitnessArcLits[i] != lit_Undef)
		{
#ifdef DEEP_GENERALIZED_REACH_DEBUG
			printf("generalized reachability: arc %d (non-bridge witness for arc %d) is being watched for bridge propagation.\n", ConvertLiteralToInt(Tree.nonBridgeWitnessArcLits[i]), ConvertLiteralToInt(Tree.DFSTree.InnerTree.getParentArcLit(Tree.DFSTree.nodeOrderings[i])));
#endif
			BridgeWatchedArcLits.insert(Tree.nonBridgeWitnessArcLits[i].x);
		}

	Initialized = true;

	for (int i = 0; i < Tree.bridgeCount; i++)
	{
		int bridgeTargetNodePos = Tree.bridgeNodePoses[i];
		if (Tree.DFSTree.subtreeUsefulnessWitness[bridgeTargetNodePos] < 0)
			continue;

		int bridgeTargetNode = Tree.DFSTree.nodeOrderings[bridgeTargetNodePos];
		Lit bridgeArcLit = Tree.DFSTree.InnerTree.getParentArcLit(bridgeTargetNode);

		int assertedDestNode = Tree.DFSTree.nodeOrderings[Tree.DFSTree.subtreeUsefulnessWitness[bridgeTargetNodePos]];
		Lit assertedDestLit = DestinationsMap.valueOf(assertedDestNode);

		if ((SolverInstance->value(bridgeArcLit) == l_Undef) && (SolverInstance->value(assertedDestLit) == l_True))
		{
			bool satisfiedClause = false;
			int undefLiteralCount = 0;

			// If the bridge is on the path to an enabled target then it should be propagated as true
			// Otherwise, there is no unit information that can be propagated. This is because both
			// the target's reachability and the bridge arc's satisfiability are unknown.
			int targetStartPos = bridgeTargetNodePos;
			int targetEndPos = targetStartPos + Tree.sizes[targetStartPos];

			reach_clause.clearunboxed();
			reach_clause.push(~assertedDestLit);

			// We define a cut (S,V\S) with S being the set of nodes that are reachable
			// from source without using the arc "Tree.bridgeArcVars[i]".
			//
			// We then add a clause containing all arcs in the cut (S,V\S).
			//
			// We do this in two steps: first for nodes S_1 that, in the pre-ordering,
			// come before vertex "arcTargetNode".
			// Note that S_1 = {nodeOrderings[j] | 0 <= j < targetStartPos}
			for (int j = 0; j < targetStartPos; j++)
			{
				if (satisfiedClause)
					break;
				if (undefLiteralCount > 1)
					break;

				int currentNode = Tree.DFSTree.nodeOrderings[j];
				SATGraph::Arc *curArc = Graph->getArcs(currentNode);
				for (int k = 0; k < Graph->getArcCount(currentNode); k++, curArc++)
				{
					int arcEndNode = curArc->succNode;
					if ((!Tree.DFSTree.InnerTree.hasCurrentTag(arcEndNode)) ||
					    ((Tree.DFSTree.reverseOrderings[arcEndNode] >= targetStartPos) &&
					     (Tree.DFSTree.reverseOrderings[arcEndNode] < targetEndPos)))
						if (Graph->isBackwardReachable(assertedDestNode, arcEndNode))
						{
							Lit newLit = curArc->arcLit;
							if (SolverInstance->value(newLit) == l_True)
							{
								satisfiedClause = true;
								break;
							}
							else if (SolverInstance->value(newLit) == l_Undef)
							{
								undefLiteralCount++;
								if (undefLiteralCount > 1)
									break;
							}

							reach_clause.push(newLit);
						}
				}
			}

			// Then, we do it for nodes S_2 that, in the pre-ordering, come after every
			// node in the subtree of "arcTargetNode"
			// Again, note that S_2 = {nodeOrderings[j] | targetEndPos <= j < treeSize }
			for (int j = targetEndPos; j < Tree.DFSTree.treeSize; j++)
			{
				if (satisfiedClause)
					break;
				if (undefLiteralCount > 1)
					break;

				int currentNode = Tree.DFSTree.nodeOrderings[j];
				SATGraph::Arc *curArc = Graph->getArcs(currentNode);
				for (int k = 0; k < Graph->getArcCount(currentNode); k++, curArc++)
				{
					int arcEndNode = curArc->succNode;
					if ((!Tree.DFSTree.InnerTree.hasCurrentTag(arcEndNode)) ||
					    ((Tree.DFSTree.reverseOrderings[arcEndNode] >= targetStartPos) &&
					     (Tree.DFSTree.reverseOrderings[arcEndNode] < targetEndPos)))
						if (Graph->isBackwardReachable(assertedDestNode, arcEndNode))
						{
							Lit newLit = curArc->arcLit;
							if (SolverInstance->value(newLit) == l_True)
							{
								satisfiedClause = true;
								break;
							}
							else if (SolverInstance->value(newLit) == l_Undef)
							{
								undefLiteralCount++;
								if (undefLiteralCount > 1)
									break;
							}

							reach_clause.push(newLit);
						}
				}
			}

#ifdef DEEP_GENERALIZED_REACH_DEBUG
			if (satisfiedClause)
				printf("generalized reachability: no propagation because clause is already satisfied\n");
			else if (undefLiteralCount == 1)
			{
				printf("generalized reachability: learnt literal %i with reason ", ConvertLiteralToInt(bridgeArcLit));
				for (int i = 0; i < reach_clause.size(); i++)
					printf("%i ", ConvertLiteralToInt(reach_clause[i]));
				printf("\n");
			}
			else
				printf("generalized reachability: no propagation because of having more than 1 undef literal\n");
#endif

			assert(satisfiedClause || (undefLiteralCount > 0));
			if (!satisfiedClause && (undefLiteralCount == 1))
			{
				Propagator::Effect e = addNewClause(reach_clause, false);
				assert((e != CONFLICT) && (e != NO_EFFECT));
				if (SolverInstance->lazy_propagation || (e == DESTRUCTIVE_PROPAGATION))
					return true;
			}
		}
	}

	return true;
}

/*________________________________________________________________________
|
| propagateReachability
|
| Description:
|   When an arc in the graph is set to FALSE, check for bridge edges
|   and infer arcs that must hold for two nodes to remain reachable.
|
|___________________________________________________________________________*/

bool GeneralizedReachabilityPropagator::propagate(int start, int end)
{
#ifdef DEEP_GENERALIZED_REACH_DEBUG
	printf("generalized reachability: propagating trail literals from position %d to position %d\n", start, end);
#endif

	bool newDFSTreeComputationNeeded = false;
	bool nonreachabilityTestNeeded = false;
	bool bridgePropagationNeeded = !Initialized;

	for (int i = start; i < end; i++)
	{
		Lit p = getTrailLiteralAt(i);

#ifdef DEEP_GENERALIZED_REACH_DEBUG
		printf("generalized reachability: considering literal %i\n", ConvertLiteralToInt(p));
#endif

		bool isDestLit = DestinationLits.hasMember(p.x);

		if (!isDestLit && !(Graph->isGraphArc(p) && (Graph->label(p) == ~p)))
			continue; // We only care about propagation of "p" when either "p"
								// enables a new destination or when "~p" is a graph arc
								// (i.e., "p" disables an arc).

		newDFSTreeComputationNeeded |= TreeEdgeLits.hasMember((~p).x);
		nonreachabilityTestNeeded |= newDFSTreeComputationNeeded || isDestLit;
		bridgePropagationNeeded |= 	nonreachabilityTestNeeded || isDestLit || BridgeWatchedArcLits.hasMember((~p).x);

		if (newDFSTreeComputationNeeded)
			break; // we need to do all computations
	}


	if (bridgePropagationNeeded)
		return !performPropagations(newDFSTreeComputationNeeded, nonreachabilityTestNeeded);
	else
		return false;
}

bool GeneralizedReachabilityPropagator::propagate(Minisat::Lit p)
{
#ifdef DEEP_GENERALIZED_REACH_DEBUG
	printf("generalized reachability: propagating %i\n", ConvertLiteralToInt(p));
#endif
	bool isDestLit = DestinationLits.hasMember(p.x);
	if (!isDestLit && !(Graph->isGraphArc(p) && (Graph->label(p) == ~p)))
		return false; // We only care about propagating "p" when either "p"
									// enables a new destination or when "~p" is a graph
									// arc (i.e., "p" disables an arc).

	bool newDFSTreeComputationNeeded = TreeEdgeLits.hasMember((~p).x);
	bool nonreachabilityTestNeeded = newDFSTreeComputationNeeded || isDestLit;

// if non-bridge witnesses are computed, then bridge propagation is only
// needed when either an arc in the spanning tree T becomes false or
// when an arc from non-bridge-witnesses becomes false
	if (!Initialized || isDestLit || BridgeWatchedArcLits.hasMember((~p).x))
		return !performPropagations(newDFSTreeComputationNeeded, nonreachabilityTestNeeded);
	else
		return false;
}

void GeneralizedReachabilityPropagator::cancelUntil(int level)
{
	Initialized = false;
}

const vec<Lit> &GeneralizedReachabilityPropagator::explain()
{
	auto fstOutInModel = [this](int node) -> int { return genReachFirstInModelOutArcIndex(Graph, SolverInstance, node); };
	auto lstOut = [this](int node) -> int { return Graph->getArcCount(node); };
	auto nextOutInModel = [this](int node, int curIndex) -> int { return genReachNextInModelOutArcIndex(Graph, SolverInstance, node, curIndex); };
	auto outArcByIdx = [this](int node, int curIndex) -> SATGraph::Arc* { return Graph->getArcs(node) + curIndex; };

	DFSwithDummyVisitFollow<decltype(fstOutInModel), decltype(lstOut), decltype(nextOutInModel), decltype(outArcByIdx)>(
		Source, Tree.DFSTree, fstOutInModel, lstOut, nextOutInModel, outArcByIdx);

	auto inModelDests = [this](int node) -> bool
		{
			return DestinationsMap.hasKey(node) ? (SolverInstance->modelValue(DestinationsMap.valueOf(node)) == l_True) : false;
		};
	findUsefulSubtrees<decltype(inModelDests)>(Tree.DFSTree, inModelDests);

	for (auto it = DestinationNodes.cbegin(); it != DestinationNodes.cend(); it++)
		if (SolverInstance->modelValue(DestinationsMap.valueOf(*it)) == l_False)
			reach_clause.push(~DestinationsMap.valueOf(*it));

	reach_clause.clear();
	for (int i = 0; i < Tree.DFSTree.treeSize; i++)
		if (Tree.DFSTree.subtreeUsefulnessWitness[i] >= 0)
			reach_clause.push(Tree.DFSTree.InnerTree.getParentArcLit(Tree.DFSTree.nodeOrderings[i]));

	return reach_clause;
}

Propagator *GeneralizedReachabilityPropagator::copy(Solver *S)
{
	unordered_map<int, Lit> DestNodes;

	for (auto it = DestinationNodes.cbegin(); it != DestinationNodes.cend(); it++)
		DestNodes[*it] = DestinationsMap.valueOf(*it);

	return new GeneralizedReachabilityPropagator(S, S->nVars(), Graph, Source, DestNodes);
}

