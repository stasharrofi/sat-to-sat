
#include "ReachabilityPropagator.h"

#define noREACHDEBUG

#ifdef REACHDEBUG
#define noREACHDEBUG_LEVEL_2
#endif

#ifdef PROPAGATOR_DEBUG
#ifdef REACHDEBUG
static const char *reachPropName = "reach";
#endif
#endif

ReachabilityPropagator::ReachabilityPropagator(Solver *S, int nOfVars, SATGraph *G, int SourceNode, const unordered_set<int> &DestNodes)
	: Propagator(S),
		DestinationsSet(G->nodeCount + 1),
		Tree(G->nodeCount),
		TreeEdgeLits(nOfVars * 2 + 3),
		BridgeWatchedArcLits(nOfVars * 2 + 3)
{
#ifdef PROPAGATOR_DEBUG
#ifdef REACHDEBUG
	debuggingEnabled = true;
	propagatorName = reachPropName;
#endif
#endif
	Graph = G;
	Source = SourceNode;
	for (auto it = DestNodes.cbegin(); it != DestNodes.cend(); it++)
	{
		DestinationsSet.insert(*it);
		DestinationsList.push_back(*it);
	}

	Initialized = false;
}

bool ReachabilityPropagator::initialize(void)
{
#ifdef REACHDEBUG
	printf("reachability: initializing\n");
#endif
	return performPropagations(true);
}

bool ReachabilityPropagator::isTheoryVar(Var v)
{
  return Graph->isGraphArc(v);
}

inline int reachFirstPossibleOutArcIndex(SATGraph *G, Solver *S, int node)
{
	SATGraph::Arc *arcs = G->getArcs(node);

	for (int i = 0; i < G->getArcCount(node); i++)
		if (S->value(arcs[i].arcLit) != l_False)
			return i;

	return G->getArcCount(node);
}

inline int reachNextPossibleOutArcIndex(SATGraph *G, Solver *S, int node, int curIndex)
{
	SATGraph::Arc *arcs = G->getArcs(node);

	for (int i = curIndex + 1; i < G->getArcCount(node); i++)
		if (S->value(arcs[i].arcLit) != l_False)
			return i;

	return G->getArcCount(node);
}

inline int reachFirstInModelOutArcIndex(SATGraph *G, Solver *S, int node)
{
	SATGraph::Arc *arcs = G->getArcs(node);

	for (int i = 0; i < G->getArcCount(node); i++)
		if (S->modelValue(arcs[i].arcLit) != l_False)
			return i;

	return G->getArcCount(node);
}

inline int reachNextInModelOutArcIndex(SATGraph *G, Solver *S, int node, int curIndex)
{
	SATGraph::Arc *arcs = G->getArcs(node);

	for (int i = curIndex + 1; i < G->getArcCount(node); i++)
		if (S->modelValue(arcs[i].arcLit) != l_False)
			return i;

	return G->getArcCount(node);
}

inline int reachFirstPossibleInArcIndex(SATGraph *G, Solver *S, int node)
{
	SATGraph::Arc *arcs = G->getInverseArcs(node);

	for (int i = 0; i < G->getInverseArcCount(node); i++)
		if (S->value(arcs[i].arcLit) != l_False)
			return i;

	return G->getInverseArcCount(node);
}

inline int reachNextPossibleInArcIndex(SATGraph *G, Solver *S, int node, int curIndex)
{
	SATGraph::Arc *arcs = G->getInverseArcs(node);

	for (int i = curIndex + 1; i < G->getInverseArcCount(node); i++)
		if (S->value(arcs[i].arcLit) != l_False)
			return i;

	return G->getInverseArcCount(node);
}

bool ReachabilityPropagator::performPropagations(bool checkNonreachability)
{
	if (!Initialized || checkNonreachability)
	{
		auto fstOut = [this](int node) -> int { return reachFirstPossibleOutArcIndex(Graph, SolverInstance, node); };
		auto lstOut = [this](int node) -> int { return Graph->getArcCount(node); };
		auto nextOut = [this](int node, int curIndex) -> int { return reachNextPossibleOutArcIndex(Graph, SolverInstance, node, curIndex); };
		auto outArcByIdx = [this](int node, int curIndex) -> SATGraph::Arc* { return Graph->getArcs(node) + curIndex; };

		DFSwithDummyVisitFollow<decltype(fstOut), decltype(lstOut), decltype(nextOut), decltype(outArcByIdx)>(
			Source, Tree.DFSTree, fstOut, lstOut, nextOut, outArcByIdx);

		for(auto it = DestinationsList.cbegin(); it != DestinationsList.cend(); ++it)
		{
			int destNode = (*it);
			if (!Tree.DFSTree.InnerTree.hasCurrentTag(destNode))
			{
				reach_clause.clearunboxed();
				for (int i = 0; i < Tree.DFSTree.treeSize; i++)
				{
					int curNode = Tree.DFSTree.nodeOrderings[i];
					auto arcList = Graph->getArcs(curNode);
					for(int j = 0; j < Graph->getArcCount(curNode); j++)
						if (!Tree.DFSTree.InnerTree.hasCurrentTag(arcList[j].succNode))
							if (Graph->isBackwardReachable(destNode, arcList[j].succNode))
								reach_clause.push(arcList[j].arcLit);
				}

#ifdef REACHDEBUG
				printf("reachability: conflict clause found: ");
				for (int i = 0; i < reach_clause.size(); i++)
					printf("%i ", ConvertLiteralToInt(reach_clause[i]));
				printf("\n");
#endif
				Propagator::Effect e = addNewClause(reach_clause, false);
				return (e != CONFLICT);
			}
		}

		auto keepDests = [this](int node) -> bool { return DestinationsSet.hasMember(node); };
		findUsefulSubtrees<decltype(keepDests)>(Tree.DFSTree, keepDests);

#ifdef REACHDEBUG_LEVEL_2
		printf("reachability: following arcs are being watch for non-reachability: ");
#endif
		TreeEdgeLits.clear();
		for (int i = 1; i < Tree.DFSTree.treeSize; i++)
			if (Tree.DFSTree.subtreeUsefulnessWitness[i] >= 0)
			{
#ifdef REACHDEBUG_LEVEL_2
				printf("%d ", ConvertLiteralToInt(Tree.DFSTree.InnerTree.getParentArcLit(Tree.DFSTree.nodeOrderings[i])));
#endif
				TreeEdgeLits.insert(Tree.DFSTree.InnerTree.getParentArcLit(Tree.DFSTree.nodeOrderings[i]).x);
			}
#ifdef REACHDEBUG_LEVEL_2
		printf("\n");
#endif
	}


#ifdef COMPUTE_NON_BRIDGE_WITNESSES
#ifdef REACHDEBUG_LEVEL_2
	printf("reachability: following arcs are being watched for bridge propagation:");
#endif
	BridgeWatchedArcLits.clear();
	for (int i = 1; i < Tree.DFSTree.treeSize; i++)
	{
#ifdef REACHDEBUG_LEVEL_2
		printf("%d ", ConvertLiteralToInt(Tree.DFSTree.InnerTree.getParentArcLit(Tree.DFSTree.nodeOrderings[i])));
#endif
		BridgeWatchedArcLits.insert(Tree.DFSTree.InnerTree.getParentArcLit(Tree.DFSTree.nodeOrderings[i]).x);
	}
#ifdef REACHDEBUG_LEVEL_2
	printf("\n");
#endif
#endif

	auto fstIn = [this](int node) -> int { return reachFirstPossibleInArcIndex(Graph, SolverInstance, node); };
	auto lstIn = [this](int node) -> int { return Graph->getInverseArcCount(node); };
	auto nextIn = [this](int node, int curIndex) -> int { return reachNextPossibleInArcIndex(Graph, SolverInstance, node, curIndex); };
	auto inArcByIdx = [this](int node, int curIndex) -> SATGraph::Arc* { return Graph->getInverseArcs(node) + curIndex; };

	findBridges<decltype(fstIn), decltype(lstIn), decltype(nextIn), decltype(inArcByIdx)>(Tree, fstIn, lstIn, nextIn, inArcByIdx);

	bool lazyPropCompleted = false;
	for (int i = 0; i < Tree.bridgeCount; i++)
	{
		int bridgeTargetNodePos = Tree.bridgeNodePoses[i];
		int bridgeTargetNode = Tree.DFSTree.nodeOrderings[bridgeTargetNodePos];
		Lit bridgeArcLit = Tree.DFSTree.InnerTree.getParentArcLit(bridgeTargetNode);
		if (SolverInstance->value(bridgeArcLit) == l_Undef)
			if (Tree.DFSTree.subtreeUsefulnessWitness[bridgeTargetNodePos] >= 0)
			{
				int targetStartPos = bridgeTargetNodePos;
				int targetEndPos = targetStartPos + Tree.sizes[targetStartPos];

				reach_clause.clearunboxed();
				int destNode = Tree.DFSTree.nodeOrderings[Tree.DFSTree.subtreeUsefulnessWitness[targetStartPos]];

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
					int currentNode = Tree.DFSTree.nodeOrderings[j];
					for (int k = 0; k < Graph->getArcCount(currentNode); k++)
					{
						SATGraph::Arc arc = Graph->getArcs(currentNode)[k];
						int arcEndNode = arc.succNode;
						if ((!Tree.DFSTree.InnerTree.hasCurrentTag(arcEndNode)) ||
						    ((Tree.DFSTree.reverseOrderings[arcEndNode] >= targetStartPos) &&
						     (Tree.DFSTree.reverseOrderings[arcEndNode] < targetEndPos)))
							if (Graph->isBackwardReachable(destNode, arcEndNode))
								reach_clause.push(arc.arcLit);
					}
				}

				// Then, we do it for nodes S_2 that, in the pre-ordering, come after every
				// node in the subtree of "arcTargetNode"
				// Again, note that S_2 = {nodeOrderings[j] | targetEndPos <= j < treeSize }
				for (int j = targetEndPos; j < Tree.DFSTree.treeSize; j++)
				{
					int currentNode = Tree.DFSTree.nodeOrderings[j];
					for (int k = 0; k < Graph->getArcCount(currentNode); k++)
					{
						SATGraph::Arc arc = Graph->getArcs(currentNode)[k];
						int arcEndNode = arc.succNode;
						if ((!Tree.DFSTree.InnerTree.hasCurrentTag(arcEndNode)) ||
						    ((Tree.DFSTree.reverseOrderings[arcEndNode] >= targetStartPos) &&
							   (Tree.DFSTree.reverseOrderings[arcEndNode] < targetEndPos)))
							if (Graph->isBackwardReachable(destNode, arcEndNode))
								reach_clause.push(arc.arcLit);
					}
				}

#ifdef REACHDEBUG
				printf("reachability: learnt literal %i with reason ", ConvertVarToInt(bridgeArcVar));
				for (int i = 0; i < reach_clause.size(); i++)
					printf("%i ", ConvertLiteralToInt(reach_clause[i]));
				printf("\n");
#endif

				Propagator::Effect e = addNewClause(reach_clause, lazyPropCompleted);
				switch (e)
				{
					case CONFLICT: return false;
					case DESTRUCTIVE_PROPAGATION: return true;
					default: break;
				}
				if (SolverInstance->lazy_propagation)
					break;
			}
	}

#ifdef COMPUTE_NON_BRIDGE_WITNESSES
#ifdef REACHDEBUG_LEVEL_2
	printf("reachability: non-bridge witnesses for bridge propagation of form arc --> witness: ");
#endif
	for (int i = 1; i < Tree.DFSTree.treeSize; i++)
		if (Tree.nonBridgeWitnessArcLits[i] != lit_Undef)
		{
#ifdef REACHDEBUG_LEVEL_2
			printf("%d --> %d, ", ConvertLiteralToInt(Tree.nonBridgeWitnessArcLits[i]), ConvertLiteralToInt(Tree.DFSTree.InnerTree.getParentArcLit(Tree.DFSTree.nodeOrderings[i])));
#endif
			BridgeWatchedArcLits.insert(Tree.nonBridgeWitnessArcLits[i].x);
		}
#ifdef REACHDEBUG_LEVEL_2
	printf("\n");
#endif

#endif
	Initialized = true;

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

bool ReachabilityPropagator::propagate(int start, int end)
{
#ifdef REACHDEBUG
	printf("reachability: propagating trail literals from position %d to position %d\n", start, end);
#endif

	bool nonreachabilityTestNeeded = false;
#ifdef PROPAGATEBRIDGES
#ifdef COMPUTE_NON_BRIDGE_WITNESSES
	bool bridgePropagationNeeded = !Initialized;
#endif
#endif

	for (int i = start; i < end; i++)
	{
		Lit p = getTrailLiteralAt(i);

		if (!Graph->isGraphArc(Minisat::var(p))) continue;	// Literal is not an arc, exit.

		nonreachabilityTestNeeded |= TreeEdgeLits.hasMember((~p).x);
#ifdef PROPAGATEBRIDGES
#ifdef COMPUTE_NON_BRIDGE_WITNESSES
		// if non-bridge witnesses are computed, then bridge propagation is only
		// needed when either an arc in the spanning tree T becomes false or
		// when an arc from non-bridge-witnesses becomes false
		bridgePropagationNeeded |= nonreachabilityTestNeeded || BridgeWatchedArcLits.hasMember((~p).x);
#endif
#endif
		if (nonreachabilityTestNeeded)
			break; // It cannot get more true than this. Stop looking more.
	}

#ifdef PROPAGATEBRIDGES

#ifdef COMPUTE_NON_BRIDGE_WITNESSES
	if (bridgePropagationNeeded)
		return !performPropagations(nonreachabilityTestNeeded);
	else
		return false;
#else
	return !performPropagations(nonreachabilityTestNeeded);
#endif

#else
	return !performPropagations(nonreachabilityTestNeeded);
#endif
}

bool ReachabilityPropagator::propagate(Minisat::Lit p)
{
#ifdef REACHDEBUG
	printf("reachability: propagating %i\n", ConvertLiteralToInt(p));
#endif
  if (!Graph->isGraphArc(var(p))) return false;	// Literal is not an arc, exit.

#ifdef PROPAGATEBRIDGES

#ifdef COMPUTE_NON_BRIDGE_WITNESSES
// if non-bridge witnesses are computed, then bridge propagation is only
// needed when either an arc in the spanning tree T becomes false or
// when an from non-bridge-witnesses becomes false
	if (!Initialized || BridgeWatchedArcLits.hasMember((~p).x))
		return !performPropagations(TreeEdgeLits.hasMember((~p).x));
	else
		return false;
#else
// otherwise, bridge propagation is always performed
	return !performPropagations(!Initialized || TreeEdgeLits.hasMember((~p).x));
#endif

#else
	return !performPropagations(!Initialized || TreeEdgeLits.hasMember((~p).x));
#endif
}

void ReachabilityPropagator::cancelUntil(int level)
{
	Initialized = false;
}

const vec<Lit> &ReachabilityPropagator::explain()
{
	auto fstOutInModel = [this](int node) -> int { return reachFirstInModelOutArcIndex(Graph, SolverInstance, node); };
	auto lstOut = [this](int node) -> int { return Graph->getArcCount(node); };
	auto nextOutInModel = [this](int node, int curIndex) -> int { return reachNextInModelOutArcIndex(Graph, SolverInstance, node, curIndex); };
	auto outArcByIdx = [this](int node, int curIndex) -> SATGraph::Arc* { return Graph->getArcs(node) + curIndex; };

	DFSwithDummyVisitFollow<decltype(fstOutInModel), decltype(lstOut), decltype(nextOutInModel), decltype(outArcByIdx)>(
		Source, Tree.DFSTree, fstOutInModel, lstOut, nextOutInModel, outArcByIdx);

	auto keepDests = [this](int node) -> bool { return DestinationsSet.hasMember(node); };
	findUsefulSubtrees<decltype(keepDests)>(Tree.DFSTree, keepDests);

	reach_clause.clear();
	for (int i = 0; i < Tree.DFSTree.treeSize; i++)
		if (Tree.DFSTree.subtreeUsefulnessWitness[i] >= 0)
			reach_clause.push(Tree.DFSTree.InnerTree.getParentArcLit(Tree.DFSTree.nodeOrderings[i]));

	return reach_clause;
}

Propagator *ReachabilityPropagator::copy(Solver *S)
{
	unordered_set<int> DestNodes;

	for (auto it = DestinationsList.cbegin(); it != DestinationsList.cend(); it++)
		DestNodes.insert(*it);

	return new ReachabilityPropagator(S, S->nVars(), Graph, Source, DestNodes);
}

