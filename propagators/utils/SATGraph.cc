
#include "core/SolverTypes.h"
#include "core/Solver.h"
#include <vector>
#include "SATGraph.h"
#include "GraphUtils.h"

/*________________________________________________________________________
|
| SATgraph
|
| Description:
|   Representation of directed graphs, with support for operations needed
|   in propagating acyclicity constraints.
|
|___________________________________________________________________________*/


void SATGraph::createGraph(int nOfVars)
{
  arcSources = new int[nOfVars];
  arcTargets = new int[nOfVars];
  arcLabels = new Lit[nOfVars];

  for (int i = 0; i < nOfVars; i++)
		arcSources[i] = arcTargets[i] = -1;

  minArcIndex = 0x7fffffff;
  maxArcIndex = 0;

	forwardReachability = backwardReachability = NULL;
}

void SATGraph::initGraph(int nOfNodes)
{
	dfsTree = new OrderedDFSTree(nOfNodes);

	arcs = new NodeData[nOfNodes];
  inverseArcs = new NodeData[nOfNodes];

  for (int i = 0; i < nOfNodes; i++)
		arcs[i].arcCount = inverseArcs[i].arcCount = 0;

  nodeCount = nOfNodes;
}

void SATGraph::createNode(int node, int nOfArcs)
{
  assert(node < nodeCount);
  assert(0 <= node);

  arcs[node].arcCount = 0;
  arcs[node].arcList = new Arc[nOfArcs];

  inverseArcs[node].arcCount = 0;
}

void SATGraph::addArc(Minisat::Lit p, int node, int succNode)
{
  assert(node <= nodeCount);
  assert(succNode <= nodeCount);
  assert(0 <= node);
  assert(0 <= succNode);

	NodeData &curNode = arcs[node];
	Arc &curArc = curNode.arcList[curNode.arcCount];
	curArc.arcLit = p;
  curArc.succNode = succNode;
  curNode.arcCount++;

	Minisat::Var v = var(p);
  arcSources[v] = node;
  arcTargets[v] = succNode;
  arcLabels[v] = p;

  if (v < minArcIndex) minArcIndex = v;
  if (v > maxArcIndex) maxArcIndex = v;

  inverseArcs[succNode].arcCount++;
}

// After all arcs of the graph are known, allocate memory for and compute
// inverses of all arcs.

void SATGraph::createInverseArcs()
{
	// Number of inverse arcss is now known. Allocate memory for them.
	for (int i = 0; i < nodeCount; i++)
	{
		inverseArcs[i].arcList = new Arc[inverseArcs[i].arcCount];
		inverseArcs[i].arcCount = 0;
	}

	// Go through all arcs, and create their inverses.
	for (int i = 0; i < nodeCount; i++)
	{
		NodeData curNode = arcs[i];
		for (int j = 0; j < curNode.arcCount; j++)
		{ // Go through arcs of node i.
			Arc curArc = curNode.arcList[j];
			int succNode = curArc.succNode;
			Lit p = curArc.arcLit;

			NodeData &succInverseNode = inverseArcs[succNode];
			int index = succInverseNode.arcCount;
			// Add arc as an inverse arc for succnode.
			Arc &inversedArc = succInverseNode.arcList[index];
			inversedArc.succNode = i;
			inversedArc.arcLit = p;
			succInverseNode.arcCount = index + 1;
		}
	}
}

void SATGraph::computeForwardReachability(int node)
{
	if (forwardReachability == NULL)
	{
		forwardReachability = new bool *[nodeCount + 1];
		for (int i = 0; i <= nodeCount; i++)
			forwardReachability[i] = NULL;
	}

	if (forwardReachability[node] == NULL)
	{
		auto fst = [](int node) -> int { return 0; };
		auto lst = [this](int node) -> int { return arcs[node].arcCount; };
		auto nxt = [](int node, int curIndex) -> int { return curIndex + 1; };
		auto arcByIdx = [this](int node, int curIndex) -> Arc* { return arcs[node].arcList + curIndex; };

		DFSwithDummyVisitFollow(node, *dfsTree, fst, lst, nxt, arcByIdx);

		bool *reachabilities = new bool[nodeCount + 1];
		for (int i = 0; i < nodeCount; i++)
			reachabilities[i] = dfsTree->InnerTree.hasCurrentTag(i);
		reachabilities[nodeCount] = false;
		forwardReachability[node] = reachabilities;
	}
}

void SATGraph::computeBackwardReachability(int node)
{
	if (backwardReachability == NULL)
	{
		backwardReachability = new bool *[nodeCount + 1];
		for (int i = 0; i <= nodeCount; i++)
			backwardReachability[i] = NULL;
	}

	if (backwardReachability[node] == NULL)
	{
		auto fst = [](int node) -> int { return 0; };
		auto lst = [this](int node) -> int { return inverseArcs[node].arcCount; };
		auto nxt = [](int node, int curIndex) -> int { return curIndex + 1; };
		auto arcByIdx = [this](int node, int curIndex) -> Arc* { return inverseArcs[node].arcList + curIndex; };

		DFSwithDummyVisitFollow(node, *dfsTree, fst, lst, nxt, arcByIdx);

		bool *reachabilities = new bool[nodeCount + 1];
		for (int i = 0; i < nodeCount; i++)
			reachabilities[i] = dfsTree->InnerTree.hasCurrentTag(i);
		reachabilities[nodeCount] = false;
		backwardReachability[node] = reachabilities;
	}
}
