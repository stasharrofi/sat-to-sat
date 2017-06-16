/****************************************************************************************[Dimacs.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Minisat_Dimacs_h
#define Minisat_Dimacs_h

#include <stdio.h>
#include <stack>

#include "utils/ParseUtils.h"
#include "core/SolverTypes.h"
#include "maxsat/MaxSAT.h"

#include "propagators/utils/SATGraph.h"
#include "propagators/AcyclicityPropagator.h"
#include "propagators/ReachabilityPropagator.h"
#include "propagators/GeneralizedNonreachabilityPropagator.h"
#include "propagators/GeneralizedReachabilityPropagator.h"
#include "propagators/UnitReachabilityPropagator.h"

#include "propagators/GeneralizedPropagator.h"

using namespace std;
using namespace NSPACE;

namespace Minisat {

//=================================================================================================
// DIMACS Parser:

template<class B>
inline Lit parseLiteral(B& in) {
	int parsed_lit = parseInt(in);
	return mkLit(abs(parsed_lit) - 1, (parsed_lit < 0));
}
	
template<class B, class Solver>
static void readClause(B& in, Solver& S, vec<Lit>& lits) {
    int     parsed_lit, var;
    lits.clear();
    for (;;){
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        var = abs(parsed_lit)-1;
        while (var >= S.nVars()) S.newVar();
        lits.push( (parsed_lit > 0) ? mkLit(var) : ~mkLit(var) );
    }
}

template<class B>
static void parse_DIMACS_main(B& in, MaxSAT& S)
{
	vec<Lit> lits;
	int vars    = 0;
	int clauses = 0;
	int cnt     = 0;

	SATGraph* G = NULL;
	bool insideGraph = false;

	MaxSAT *mxsolver = &S;
	stack<Solver *> solverStack;
	stack<int> varCountStack;
	Solver *currentSolver = S.getPrototypeSolver();
	solverStack.push(currentSolver);

	for (;;){
		skipWhitespace(in);
		if (*in == EOF) break;
		else if (*in == 'p'){
			if (eagerMatch(in, "p cnf")){
				vars    = parseInt(in);
				varCountStack.push(vars);
				clauses = parseInt(in);
				while (currentSolver->nVars() < vars)
					currentSolver->newVar();
				// SATRACE'06 hack
				// if (clauses > 4000000)
				//     S.eliminate(true);
			}else{
				printf("PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
			}
		} else if (*in == 'c') {
			if (eagerMatch(in, "c ")) {
				if (eagerMatch(in, "g"))
				{
					if (eagerMatch(in, "r"))
					{
						if (eagerMatch(in, "aph")) // graph keyword
						{
							G = new SATGraph();
							G->createGraph(vars);
							G->initGraph(parseInt(in)+1);
							insideGraph = true;
						}
						else if (eagerMatch(in, "eachable")) // greachable keyword
						{
							assert(G);

							int source = parseInt(in);
							int destCount = parseInt(in);

							std::unordered_map<int, Lit> dests;
							for (int i = 0; i < destCount; i++)
							{
								int node = parseInt(in);
								Lit p = parseLiteral(in);
								dests[node] = p;

								while (currentSolver->nVars() <= var(p)) currentSolver->newVar();
							}

							currentSolver->addPropagator(new GeneralizedReachabilityPropagator(currentSolver, vars, G, source, dests));
						}
						else if (eagerMatch(in, "nonreach")) // grnonreach keyword
						{
							assert(G);

							unordered_map<int, unordered_map<int, Lit> > reachabilities;
							int reachSourceCount = parseInt(in);
							for (int i = 0; i < reachSourceCount; i++)
							{
								int source = parseInt(in);
								reachabilities[source] = unordered_map<int, Lit>();

								int destCount = parseInt(in);
								for (int j = 0; j < destCount; j++)
								{
									int dest = parseInt(in);
									Lit p = parseLiteral(in);
									reachabilities[source][dest] = p;
								}
							}

							unordered_map<int, unordered_map<int, Lit> > nonReachabilities;
							int nonreachSourceCount = parseInt(in);
							for (int i = 0; i < nonreachSourceCount; i++)
							{
								int source = parseInt(in);
								nonReachabilities[source] = unordered_map<int, Lit>();

								int destCount = parseInt(in);
								for (int j = 0; j < destCount; j++)
								{
									int dest = parseInt(in);
									Lit p = parseLiteral(in);
									nonReachabilities[source][dest] = p;
								}
							}

							currentSolver->addPropagator(new UnitReachabilityPropagator(currentSolver, G, reachabilities, nonReachabilities));
						}
					}
					else if (eagerMatch(in, "nonreach"))
					{
						assert(G);

						int pairCount = parseInt(in);

						std::vector< tuple<int, int, Lit> > nodePairsList;
						for (int i = 0; i < pairCount; i++)
						{
							int sourceNode = parseInt(in);
							int targetNode = parseInt(in);
							Lit l = parseLiteral(in);

							nodePairsList.push_back(tuple<int, int, Lit>(sourceNode, targetNode, l));

							Var v = var(l);
							while (currentSolver->nVars() <= v) currentSolver->newVar();
						}

						currentSolver->addPropagator(new GeneralizedNonreachabilityPropagator(currentSolver, vars, G, nodePairsList));
					}
				}
				else if (eagerMatch(in, "minimize"))
				{
					if (insideGraph)
						printf("PARSE ERROR! Minimize keyword inside a graph\n"), exit(3);
					if (solverStack.size() > 1)
						printf("PARSE ERROR! Minimize keyword inside a module\n"), exit(3);

					int n = parseInt(in);
					while (n != 0)
					{
						Var var = abs(n) - 1;
						while (var >= currentSolver->nVars())
							currentSolver->newVar();

						lits.clear();
						lits.push((n > 0) ? ~mkLit(var) : mkLit(var));

						int64_t weight = parseInt(in);

						if (weight >= ((int64_t) INT32_MAX))
							printf("PARSE ERROR! Weight exceeds maximum weight\n"), exit(3);
						if (weight <= 0)
							printf("PARSE ERROR! Weight should be nonnegative\n"), exit(3);

						// Updates the maximum weight of soft clauses.
						mxsolver->setCurrentWeight((int) weight);
						// Updates the sum of the weights of soft clauses.
						mxsolver->updateSumWeights((int) weight);

						mxsolver->addSoftClause((int) weight, lits);

						n = parseInt(in);
					}
				}
				else if (eagerMatch(in, "node"))
				{
					assert(G);
					int n = parseInt(in);
					int a = parseInt(in);
					G->createNode(n,a);
				}
				else if (eagerMatch(in, "a"))
				{
					if (eagerMatch(in, "rc")) // "arc" keyword found
					{
						assert(G);
						Lit ap = parseLiteral(in);
						int as = parseInt(in);
						int at = parseInt(in);
						G->addArc(ap,as,at);
						while(var(ap) >= currentSolver->nVars()) currentSolver->newVar();
					}
					else if (eagerMatch(in, "cyc")) // "acyc" keyword found
					{
						assert(G);
						currentSolver->addPropagator(new AcyclicityPropagator(currentSolver, G));
					}
				}
				else if (eagerMatch(in, "end"))
				{
					if (eagerMatch(in, "graph"))
					{
						assert(G);
						G->createInverseArcs();
						insideGraph = false;
					}
					else if (eagerMatch(in, "propagator"))
					{
						assert(solverStack.size() > 1);
						if (insideGraph)
							fprintf(stderr, "WARNING! Generalized propagator started inside graph definition.\n");
						solverStack.pop();
						varCountStack.pop();
						currentSolver = solverStack.top();
						vars = varCountStack.top();
					}
				}
				else if (eagerMatch(in, "reachable"))
				{
					assert(G);

					int source = parseInt(in);
					int destCount = parseInt(in);

					std::unordered_set<int> dests;
					for (int i = 0; i < destCount; i++)
						dests.insert(parseInt(in));

					currentSolver->addPropagator(new ReachabilityPropagator(currentSolver, vars, G, source, dests));
				}
				else if (eagerMatch(in, "propagator"))
				{
					Solver *internalSolver = Solver::newSolver();
					solverStack.push(internalSolver);

					int n;
					int internalSolverVarCount = parseInt(in);
					varCountStack.push(internalSolverVarCount);
					while (internalSolver->nVars() < internalSolverVarCount)
						internalSolver->newVar();

					bool hasCompleteEncoding = (parseInt(in) > 0);

					vector< pair<Var, Var> > upperbounds;
					n = parseInt(in); // the number of upperbound mappings
					for (int i = 0; i < n; i++)
					{
						Var externalVar = parseInt(in) - 1;
						Var internalVar = parseInt(in) - 1;
						upperbounds.push_back(pair<Var, Var>(externalVar, internalVar));

						while (currentSolver->nVars() <= externalVar) currentSolver->newVar();
						while (internalSolver->nVars() <= internalVar) internalSolver->newVar();
					}

					vector< pair<Var, Var> > lowerbounds;
					n = parseInt(in); // the number of lowerbound mappings
					for (int i = 0; i < n; i++)
					{
						Var externalVar = parseInt(in) - 1;
						Var internalVar = parseInt(in) - 1;
						lowerbounds.push_back(pair<Var, Var>(externalVar, internalVar));

						while (currentSolver->nVars() <= externalVar) currentSolver->newVar();
						while (internalSolver->nVars() <= internalVar) internalSolver->newVar();
					}

					vector< pair<Lit, vector<Lit> > > reasonGenerator;
					reasonGenerator.clear();
					n = parseInt(in); // the number of atoms that might be in the reason
					for (int i = 0; i < n; i++)
					{
						Lit externalLit = parseLiteral(in);
						reasonGenerator.push_back(pair<Lit, vector<Lit> >(externalLit, vector<Lit>()));
						reasonGenerator[i].first = externalLit;

						int m = parseInt(in);
						for (int j = 0; j < m; j++)
						{
							Lit internalLit = parseLiteral(in);
							reasonGenerator[i].second.push_back(internalLit);

							Var internalVar = var(internalLit);
							while (internalSolver->nVars() <= internalVar) internalSolver->newVar();
						}

						Var externalVar = var(externalLit);
						while (currentSolver->nVars() <= externalVar) currentSolver->newVar();
					}

					TriggerProtectedPropagator *prop = new GeneralizedPropagator(currentSolver, internalSolver, hasCompleteEncoding, vars, internalSolverVarCount, upperbounds, lowerbounds, reasonGenerator);
					currentSolver->addPropagator(prop);
					currentSolver = internalSolver;
					vars = internalSolverVarCount;
				}
				else if (*in >= '0' && *in <= '9')
				{ // reading variable name
					int var = parseInt(in) - 1;
					if (var < 0)
						fprintf(stderr, "PARSE ERROR! Variable number should be at least one.\n"), exit(3);
					skipWhitespace(in);

					std::string variableName = "";
					while (*in != '\n')
					{
						variableName += *in;
						++in;
					}

					while (currentSolver->nVars() <= var)
						currentSolver->newVar();
					currentSolver->setVariableName(var, variableName);
				}
			}
			skipLine(in);
		}
		else{
			cnt++;
			readClause(in, *currentSolver, lits);
			currentSolver->addClause_(lits);
			if (solverStack.size() == 1)
				mxsolver->addHardClause(lits);
		}
	}
	if (solverStack.size() != 1)
		fprintf(stderr, "WARNING! Extended dimacs contains wrong number of 'c endpropagator' lines.\n");
	if (vars != currentSolver->nVars())
		fprintf(stderr, "WARNING! DIMACS header mismatch: wrong number of variables.\n");
	if (currentSolver->nClauses() != clauses)
		fprintf(stderr, "WARNING! DIMACS header mismatch: wrong number of clauses.\n");

	mxsolver->initialize();
}

// Inserts problem into solver.
//
template<class Solver>
static void parse_DIMACS(gzFile input_stream, Solver& S) {
    StreamBuffer in(input_stream);
    parse_DIMACS_main(in, S); }

//=================================================================================================
}

#endif
