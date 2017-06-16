
#ifndef GRAPH_UTILS_H
#define GRAPH_UTILS_H

#include "string.h"
#include <unordered_set>

#include "core/SolverTypes.h"
#include "SATGraph.h"
#include "FixedSizeStack.h"

using namespace std;
using namespace Minisat;

#define COMPUTE_NON_BRIDGE_WITNESSES

/* RootedTree struct:
 *   The bare essentials for representing a search tree including tags,
 *   parents, and parentArcVars of nodes
 */
struct RootedTree
{
	int capacity, currentTag;
	int *nodeTags;
	int *parents;
	Lit *parentArcLits;

	RootedTree(int size);

	void newTag() { currentTag++; }
	void tag(int node) { nodeTags[node] = currentTag; }

	int getParent(int node) const { return parents[node]; }
	void setParent(int node, int parent) { parents[node] = parent; }

	Lit getParentArcLit(int node) const { return parentArcLits[node]; }
	void setParentArcLit(int node, Lit parentArcLit) { parentArcLits[node] = parentArcLit; }

	bool hasCurrentTag(int node) const { return currentTag == nodeTags[node]; }
	bool hasPreviousTag(int node) const { return currentTag - 1 == nodeTags[node]; }

	// Copies the contents (not the pointers) from another rooted tree.
	// Pointers will not change. Capacity of the source should be the same as
	// the capacity of current structure.
	void copyFrom(const RootedTree &source);
};

/* OrderedDFSTree:
 *   Struct used to save a DFS tree plus its pre-orderings (i.e., parent comes
 *   before its children in the ordering), its reverse pre-ordering (i.e., where
 *   in the ordering each node comes) and the number of children for each node.
 */
struct OrderedDFSTree
{
	RootedTree InnerTree;

	int treeSize;

	int *nodeOrderings; // nodeOrderings[i]=v means that node "v" is in the "i"-th place of ordering
	int *reverseOrderings; // reverseOrderings[v]=i is equivalent to nodeOrderings[i]=v (if "v" is in the DFS tree).
	int *childCount;
	int *subtreeUsefulnessWitness;
	FixedSizeStack<int> DFSStack;

	OrderedDFSTree(int size);

	// Copies the content (not the pointers) of one DFS tree into another
	// It does not change the memory allocations. Also, contents of subtreeUsefulnessWitness
	// and DFSStack are not copied.
	void copyFrom(const OrderedDFSTree &source);
};

/* TarjanTree:
 *   Struct used to find bridge edges according to Tarjan's algorithm.
 */
struct TarjanTree
{
	OrderedDFSTree DFSTree;

	int *lowerBounds;
	int *upperBounds;
	int *sizes;

	int bridgeCount;
	int *bridgeNodePoses;
#ifdef COMPUTE_NON_BRIDGE_WITNESSES
	Lit *nonBridgeWitnessArcLits;
#endif

	TarjanTree(int size);
};

/* IncrementalDFS(root, rootParent, rootParentArcVar, T, fst, lst, nxt, arcByIdx, visitNode, followArc):
 *   Expand an existing DFS tree starting from a new node root that is connected
 *   to rootParent through arc variable rootParentArcVar. DFS graph is implicitly
 *   given by functions fst, lst, nxt and arcByIdx. Start with node "root" and
 *   save the resulting search tree into T.
 *
 *   Functions fst, lst and nxt are used to iterate over outgoing neighbours.
 *   Function arcByIdx is then used to extract neighbour information from the
 *   iterator. Function visitNode is used to visit a node before expanding it
 *   and to terminate the search if some goal is reached. Also, function
 *   followArc is used to implement operations when an arc is expanded and/or
 *   to disallow expanding specific arcs. 
 * 
 *   The function is implemented as a template so that
 *     (1) it can be re-used,
 *     (2) it can be inlined by the compiler if need be.
 *
 *   The templates used in DFS should be as follows:
 *     FirstArcIndexFunctionType:
 *       A function that returns the index of a node's first neighbour. Similar
 *       to "typedef int (*FirstArcIndexFunctionType)(int node);"
 *     LastArcIndexFunctionType:
 *       A function that returns the index of a node's last neighbour. Similar
 *       to "typedef int (*LastArcIndexFunctionType)(int node);"
 *     NextArcIndexFunctionType:
 *       A function that, given the index of a current neighbour, returns the
 *       next neighbour's index. Similar to:
 *       typedef int (*NextArcIndexFunctionType)(int node, int curIndex);
 *     ArcByIndexFunctionType:
 *       A function that, given the index of a node's neighbour, returns the
 *       arc connecting that node to that neighbour. Similar to:
 *       typedef int (*ArcByIndexFunctionType)(int node, int neighbourIndex);
 *     VisitNodeFunctionType:
 *       Callback function to visit a node during DFS search. Should return
 *       false if the search has to be ended. Similar to:
 *       typedef bool (*VisitNodeFunctionType)(int node);
 *     FollowArcFunctionType:
 *       Callback function to follow arc expansions during DFS search. Should
 *       return false if the arc is not to be expanded. Similar to:
 *       typedef bool (*VisitArcFunctionType)(int sourceNode, int targetNode, Minisat::Var arcVar);
 *
 *   Also, this way, if functions fst, lst, nxt, nodeBuIdx, visitNode or followArc
 *   require access to the graph or solver information, functors and/or lambda
 *   expressions can be used to generate closures.
 */
template <typename FirstArcIndexFunctionType,
					typename LastArcIndexFunctionType,
					typename NextArcIndexFunctionType,
					typename ArcByIndexFunctionType,
					typename VisitNodeFunctionType,
					typename FollowArcFunctionType>
inline void IncrementalDFS(int root, int rootParent, Lit rootParentArcLit, OrderedDFSTree &T,
                           FirstArcIndexFunctionType fst, LastArcIndexFunctionType lst,
                           NextArcIndexFunctionType nxt, ArcByIndexFunctionType arcByIdx,
                           VisitNodeFunctionType visitNode, FollowArcFunctionType followArc)
{
	T.DFSStack.clear();
	T.DFSStack.push(root);
	T.InnerTree.tag(root);
	T.InnerTree.setParent(root, rootParent);
	T.InnerTree.setParentArcLit(root, rootParentArcLit);
	while (!T.DFSStack.empty())
	{
		int currentNode = T.DFSStack.top();
		T.DFSStack.pop();
		T.nodeOrderings[T.treeSize] = currentNode;
		T.reverseOrderings[currentNode] = T.treeSize;
		T.childCount[T.treeSize] = 0;
		if (!visitNode(currentNode))
			break;

		for (int i = fst(currentNode); i < lst(currentNode); i = nxt(currentNode, i))
		{
			SATGraph::Arc *arc = arcByIdx(currentNode, i);
			if (followArc(currentNode, arc->succNode, arc->arcLit))
				if (!T.InnerTree.hasCurrentTag(arc->succNode))
				{
					T.DFSStack.push(arc->succNode);
					T.childCount[T.treeSize]++;
					T.InnerTree.tag(arc->succNode);
					T.InnerTree.setParent(arc->succNode, currentNode);
					T.InnerTree.setParentArcLit(arc->succNode, arc->arcLit);
				}
		}

		T.treeSize++;
	}
}

template <typename FirstArcIndexFunctionType,
					typename LastArcIndexFunctionType,
					typename NextArcIndexFunctionType,
					typename ArcByIndexFunctionType,
					typename VisitNodeFunctionType>
inline void IncrementalDFSwithDummyFollow(int root, int rootParent, Lit rootParentArcLit, OrderedDFSTree &T,
                                          FirstArcIndexFunctionType fst, LastArcIndexFunctionType lst,
                                          NextArcIndexFunctionType nxt, ArcByIndexFunctionType arcByIdx,
                                          VisitNodeFunctionType visitNode)
{
	auto followArc = [](int s, int t, Minisat::Lit p) -> bool { return true; };
	IncrementalDFS<FirstArcIndexFunctionType, LastArcIndexFunctionType,
								 NextArcIndexFunctionType, ArcByIndexFunctionType,
								 VisitNodeFunctionType, decltype(followArc)>(root, rootParent, rootParentArcLit, T, fst, lst, nxt, arcByIdx, visitNode, followArc);
}

template <typename FirstArcIndexFunctionType,
					typename LastArcIndexFunctionType,
					typename NextArcIndexFunctionType,
					typename ArcByIndexFunctionType,
					typename FollowArcFunctionType>
inline void IncrementalDFSwithDummyVisit(int root, int rootParent, Lit rootParentArcLit, OrderedDFSTree &T,
                                         FirstArcIndexFunctionType fst, LastArcIndexFunctionType lst,
                                         NextArcIndexFunctionType nxt, ArcByIndexFunctionType arcByIdx,
                                         FollowArcFunctionType followArc)
{
	auto visitNode = [](int node) -> bool { return true; };
	IncrementalDFS<FirstArcIndexFunctionType, LastArcIndexFunctionType,
								 NextArcIndexFunctionType, ArcByIndexFunctionType,
								 decltype(visitNode), FollowArcFunctionType>(root, rootParent, rootParentArcLit, T, fst, lst, nxt, arcByIdx, visitNode, followArc);
}

template <typename FirstArcIndexFunctionType,
					typename LastArcIndexFunctionType,
					typename NextArcIndexFunctionType,
					typename ArcByIndexFunctionType>
inline void IncrementalDFSwithDummyVisitFollow(int root, int rootParent, Lit rootParentArcLit, OrderedDFSTree &T,
                                               FirstArcIndexFunctionType fst, LastArcIndexFunctionType lst,
                                               NextArcIndexFunctionType nxt, ArcByIndexFunctionType arcByIdx)
{
	auto visitNode = [](int node) -> bool { return true; };
	auto followArc = [](int s, int t, Minisat::Lit p) -> bool { return true; };
	IncrementalDFS<FirstArcIndexFunctionType, LastArcIndexFunctionType,
								 NextArcIndexFunctionType, ArcByIndexFunctionType,
								 decltype(visitNode), decltype(followArc)>(root, rootParent, rootParentArcLit, T, fst, lst, nxt, arcByIdx, visitNode, followArc);
}

template <typename FirstArcIndexFunctionType,
					typename LastArcIndexFunctionType,
					typename NextArcIndexFunctionType,
					typename ArcByIndexFunctionType,
					typename VisitNodeFunctionType,
					typename FollowArcFunctionType>
inline void DFS(int root, OrderedDFSTree &T,
                FirstArcIndexFunctionType fst, LastArcIndexFunctionType lst,
                NextArcIndexFunctionType nxt, ArcByIndexFunctionType arcByIdx,
                VisitNodeFunctionType visitNode, FollowArcFunctionType followArc)
{
	T.InnerTree.newTag();
	T.treeSize = 0;

	IncrementalDFS<FirstArcIndexFunctionType, LastArcIndexFunctionType,
								 NextArcIndexFunctionType, ArcByIndexFunctionType,
								 VisitNodeFunctionType, FollowArcFunctionType>(root, -1, lit_Undef, T, fst, lst, nxt, arcByIdx, visitNode, followArc);
}

template <typename FirstArcIndexFunctionType,
					typename LastArcIndexFunctionType,
					typename NextArcIndexFunctionType,
					typename ArcByIndexFunctionType,
					typename VisitNodeFunctionType>
inline void DFSwithDummyFollow(int root, OrderedDFSTree &T,
                               FirstArcIndexFunctionType fst, LastArcIndexFunctionType lst,
                               NextArcIndexFunctionType nxt, ArcByIndexFunctionType arcByIdx,
                               VisitNodeFunctionType visitNode)
{
	auto followArc = [](int s, int t, Minisat::Lit p) -> bool { return true; };
	DFS<FirstArcIndexFunctionType, LastArcIndexFunctionType,
			NextArcIndexFunctionType, ArcByIndexFunctionType,
			VisitNodeFunctionType, decltype(followArc)>(root, T, fst, lst, nxt, arcByIdx, visitNode, followArc);
}

template <typename FirstArcIndexFunctionType,
					typename LastArcIndexFunctionType,
					typename NextArcIndexFunctionType,
					typename ArcByIndexFunctionType,
					typename FollowArcFunctionType>
inline void DFSwithDummyVisit(int root, OrderedDFSTree &T,
                              FirstArcIndexFunctionType fst, LastArcIndexFunctionType lst,
                              NextArcIndexFunctionType nxt, ArcByIndexFunctionType arcByIdx,
                              FollowArcFunctionType followArc)
{
	auto visitNode = [](int node) -> bool { return true; };
	DFS<FirstArcIndexFunctionType, LastArcIndexFunctionType,
			NextArcIndexFunctionType, ArcByIndexFunctionType,
			decltype(visitNode), FollowArcFunctionType>(root, T, fst, lst, nxt, arcByIdx, visitNode, followArc);
}

template <typename FirstArcIndexFunctionType,
					typename LastArcIndexFunctionType,
					typename NextArcIndexFunctionType,
					typename ArcByIndexFunctionType>
inline void DFSwithDummyVisitFollow(int root, OrderedDFSTree &T,
                                    FirstArcIndexFunctionType fst, LastArcIndexFunctionType lst,
                                    NextArcIndexFunctionType nxt, ArcByIndexFunctionType arcByIdx)
{
	auto visitNode = [](int node) -> bool { return true; };
	auto followArc = [](int s, int t, Minisat::Lit p) -> bool { return true; };
	DFS<FirstArcIndexFunctionType, LastArcIndexFunctionType,
			NextArcIndexFunctionType, ArcByIndexFunctionType,
			decltype(visitNode), decltype(followArc)>(root, T, fst, lst, nxt, arcByIdx, visitNode, followArc);
}

/* findUsefulSubtrees(T, keepNode):
 *   For each subtree, finds if that subtree is useful with respect to the
 *   nodes that should be kept (i.e., nodes for which keepNode(u)==true).
 *
 *   Also, fills "subtreeUsefulnessWitness" with the index of the node that
 *   witnesses the usefulness of the current subtree.
 *
 *   In other words, "subtreeUsefulnessWitness[u]==v" means that T.nodeOrderings[v]
 *   is (1) a node that should be kept, and (2) a node that belongs to the
 *   subtree of $.nodeOrderings[u].
 *
 *   Also, subtreeUsefulnessWitness[u]==-1 means that neither T.nodeOrderings[u]
 *   nor any node in its subtree are not useful.
 *
 *   The witnessed are saved in T.subtreeUsefulnessWitness. 
 *
 *   Function keepNode is used to find if a node is important to us. Template
 *   for this function should be as follows:
 *     KeepNodeFunctionType:
 *       A function that returns true/false for each node indicating whether
 *       this node is important or not. Similar to
 *       typedef bool (*KeepNodeFunctionType)(int node);
 *
 *   Implementing keepNode as template allows us to use functors and/or lambda
 *   expressions to generate closures when needed.
 */
template <typename KeepNodeFunctionType>
inline void findUsefulSubtrees(OrderedDFSTree &T, KeepNodeFunctionType keepNode)
{
	for (int i = 0; i < T.treeSize; i++)
		T.subtreeUsefulnessWitness[i] = -1;

	for (int i = T.treeSize - 1; i > 0; i--)
	{
		if (keepNode(T.nodeOrderings[i]))
			T.subtreeUsefulnessWitness[i] = i;
		if (T.subtreeUsefulnessWitness[i] >= 0)
		{
			int parentNode = T.InnerTree.parents[T.nodeOrderings[i]];
			int parentPos = T.reverseOrderings[parentNode];
			T.subtreeUsefulnessWitness[parentPos] = T.subtreeUsefulnessWitness[i];
		}
	}
}

/* FindBridges(T, fst, lst, nxt, arcByIdx):
 *   Run Tarjan algorithm to find all the bridges in an undirected graph
 *
 *   The internal DFS tree of the Tarjan tree T should have already been
 *   initialized, i.e., this algorithm does not run DFS again. It just fills
 *   the lower and upper bounds for the current computed DFS tree T
 *
 *   Functions fst, lst and nxt are used to iterate over incoming neighbours.
 *   Function arcByIdx is then used to extract neighbour information from the
 *   iterator.
 * 
 *   To understand the containts on using these templates and the rationale
 *   behind them, refer to the explanation for DFS.
 */
template <typename FirstArcIndexFunctionType,
					typename LastArcIndexFunctionType,
					typename NextArcIndexFunctionType,
					typename ArcByIndexFunctionType>
inline void findBridges(TarjanTree &T,
                 FirstArcIndexFunctionType fst,
                 LastArcIndexFunctionType lst,
                 NextArcIndexFunctionType nxt,
                 ArcByIndexFunctionType arcByIdx)
{
	for (int i = 0; i < T.DFSTree.treeSize; i++)
		T.lowerBounds[i] = T.upperBounds[i] = i;

	T.DFSTree.DFSStack.clear();
	for (int i = T.DFSTree.treeSize - 1; i > 0; i--)
	{
		T.sizes[i] = 1;
		for (int j = 0; j < T.DFSTree.childCount[i]; j++)
		{
			T.sizes[i] += T.DFSTree.DFSStack.top();
			T.DFSTree.DFSStack.pop();
		}
		T.DFSTree.DFSStack.push(T.sizes[i]);

		int currentNode = T.DFSTree.nodeOrderings[i];
		for (int j = fst(currentNode); j < lst(currentNode); j = nxt(currentNode, j))
		{
			SATGraph::Arc *arc = arcByIdx(currentNode, j);
			int neighbourNode = arc->succNode;
			if (T.DFSTree.InnerTree.hasCurrentTag(neighbourNode))
				if (T.DFSTree.InnerTree.getParent(currentNode) != neighbourNode)
				{
					int neighbourPos = T.DFSTree.reverseOrderings[neighbourNode];

					if (T.lowerBounds[i] > T.lowerBounds[neighbourPos])
					{
						T.lowerBounds[i] = T.lowerBounds[neighbourPos];
#ifdef COMPUTE_NON_BRIDGE_WITNESSES
						T.nonBridgeWitnessArcLits[i] = arc->arcLit;
#endif
					}
					if (T.upperBounds[i] < T.upperBounds[neighbourPos])
					{
						T.upperBounds[i] = T.upperBounds[neighbourPos];
#ifdef COMPUTE_NON_BRIDGE_WITNESSES
						if (T.upperBounds[i] >= i + T.sizes[i])
							T.nonBridgeWitnessArcLits[i] = arc->arcLit;
#endif
					}
				}
		}
	}

	T.bridgeCount = 0;
	T.nonBridgeWitnessArcLits[0] = Minisat::lit_Undef;
	for (int i = 1; i < T.DFSTree.treeSize; i++)
		if ((T.lowerBounds[i] == i) && (T.upperBounds[i] < i + T.sizes[i]))
		{
			T.bridgeNodePoses[T.bridgeCount] = i;
#ifdef COMPUTE_NON_BRIDGE_WITNESSES
			T.nonBridgeWitnessArcLits[i] = Minisat::lit_Undef;
#endif
			T.bridgeCount++;
		}
}

//------- Inline functions for RootedTree structure

inline RootedTree::RootedTree(int size)
{
	nodeTags = new int[size];
	memset(nodeTags, 0, size * sizeof(int));
	parents = new int[size];
	parentArcLits = new Minisat::Lit[size];

	capacity = size;
}

inline void RootedTree::copyFrom(const RootedTree &source)
{
	assert(capacity == source.capacity);

	int copySize = capacity * sizeof(int);
	memcpy(nodeTags, source.nodeTags, copySize);
	memcpy(parents, source.parents, copySize);
	memcpy(parentArcLits, source.parentArcLits, capacity * sizeof(Minisat::Lit));
}

//------- Inline functions for OrderedDFSTree structure

inline OrderedDFSTree::OrderedDFSTree(int size)
	: InnerTree(size),
		DFSStack(size + 1)
{
	treeSize = 0;
	nodeOrderings = new int[size];
	reverseOrderings = new int[size];
	childCount = new int[size];
	subtreeUsefulnessWitness = new int[size];
}

inline void OrderedDFSTree::copyFrom(const OrderedDFSTree &source)
{
	InnerTree.copyFrom(source.InnerTree);

	int copySize = InnerTree.capacity * sizeof(int);
	treeSize = source.treeSize;
	memcpy(nodeOrderings, source.nodeOrderings, copySize);
	memcpy(reverseOrderings, source.reverseOrderings, copySize);
	memcpy(childCount, source.childCount, copySize);
}

//------- Inline functions for TarjanTree structure

inline TarjanTree::TarjanTree(int size)
	: DFSTree(size)
{
	lowerBounds = new int[size];
	upperBounds = new int[size];
	sizes = new int[size];

	bridgeCount = 0;
	bridgeNodePoses = new int[size];
#ifdef COMPUTE_NON_BRIDGE_WITNESSES
	nonBridgeWitnessArcLits = new Minisat::Lit[2 * size];
#endif
}

#endif
