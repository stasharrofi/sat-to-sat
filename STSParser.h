/****************************************************************************************[Dimacs.h]
Copyright (c) 2015, Shahab Tasharrofi, shahab.tasharrofi@gmail.com

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

#ifndef Minisat_STSParser_h
#define Minisat_STSParser_h

#include <stdio.h>
#include <vector>

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
// STS Parser:

template <class B>
static void parse_STS_main(B& in, MaxSAT& S)
{
	vec<Lit> lits;

	// Each module is comprised of a solver plus its input variables.
	// Input variables are defined as a vector of pairs of variables and the i-th pair shows
	// how that i-th input is represented internally. A pair (-1, -1) means that i-th input
	// is not used at all internally. A pair (-1, N) with N >= 0 means that i-th input is
	// only used negatively and its negative occurrences are represented by variable no. N.
	// Similarly, pair (P, -1) with P >= 0 implies that the i-th input is only used positively
	// and that its positive occurrences are represented by variable number P. Finally, a
	// pair (P, N) with both P, N >= 0 implies that the i-th input is used both positively and
	// negatively inside the module while its positive occurrences are represented by variable
	// number P and its negative occurrences by variable number N.
	vector< pair<Solver *, vector< pair<Var, Var> > > > modules;
	unordered_map<Var, int> currentInputVarToIndexMap;
	
	SATGraph* graph = NULL;
	bool insideGraph = false;
	bool insideModule = false;

	int mainSolverVarCount = 1;
	int currentSolverVarCount = 1;

	MaxSAT *mxsolver = &S;
	Solver *currentSolver = S.getPrototypeSolver();
	Solver *mainSolver = S.getPrototypeSolver();

	auto getMappedVar = [&](Var externalVar, bool isPositive) -> Var
	{
		if (!insideModule)
			return externalVar;

		auto it = currentInputVarToIndexMap.find(externalVar);
		if (it == currentInputVarToIndexMap.cend())
			return externalVar;

		int index = it->second;
		Var mappedExternalVar = (isPositive ? modules[modules.size() - 1].second[index].first : modules[modules.size() - 1].second[index].second);
		if (mappedExternalVar < 0) // this is a new positive/negative occurrence of externalVar
		{
			if ((isPositive && (modules[modules.size() - 1].second[index].second < 0)) || (!isPositive && (modules[modules.size() - 1].second[index].first < 0)))
				// since the other case is not yet found, we can use externalVar itself to represent its positive/negative occurrences
				mappedExternalVar = externalVar;
			else // a new variable should be generated to represent positive/negative occurrences of externalVar
			     // because externalVar itself is used for the other case
				mappedExternalVar = currentSolverVarCount;

			while (currentSolver->nVars() <= mappedExternalVar)
				currentSolver->newVar();
			if (currentSolverVarCount < currentSolver->nVars())
				currentSolverVarCount = currentSolver->nVars();

			if (isPositive)
				modules[modules.size() - 1].second[index].first = mappedExternalVar;
			else
				modules[modules.size() - 1].second[index].second = mappedExternalVar;
		}

		return mappedExternalVar;
	};

	for (;;){
		skipWhitespace(in);
		if (*in == EOF) break;
		else if (eagerMatch(in, "a"))
		{
			if (eagerMatch(in, "rc")) // "arc" keyword found
			{
				if (!insideGraph)
					printf("PARSE ERROR! Node keyword outside a graph\n"), exit(3);

				assert(graph);
				Lit ap = parseLiteral(in);
				int as = parseInt(in);
				int at = parseInt(in);
				graph->addArc(ap,as,at);
				while(var(ap) >= currentSolver->nVars()) currentSolver->newVar();
			}
			else if (eagerMatch(in, "cyc"))
			{
				if (insideGraph)
					printf("PARSE ERROR! Graph propagator defined inside a graph\n"), exit(3);
				if (graph == NULL)
					printf("PARSE ERROR! Graph propagator defined without defining a graph\n"), exit(3);
				if (insideModule)
					printf("PARSE ERROR! Graph propagator inside module is not currently supported\n"), exit(3);

				currentSolver->addPropagator(new AcyclicityPropagator(currentSolver, graph));
			}
			else
				printf("PARSE ERROR! Unknown keyword\n"), exit(3);
		}
		else if (*in == 'c')
		{
			if (eagerMatch(in, "c "))
			{
				if (*in >= '0' && *in <= '9')
				{ // reading variable name
					int var = parseInt(in) - 1;
					if (var < 0)
						printf("PARSE ERROR! Variable number should be at least one.\n"), exit(3);
					skipWhitespace(in);

					std::string variableName = "";
					while (*in != '\n')
					{
						variableName += *in;
						++in;
					}

					currentSolver->setVariableName(var, variableName);
				}
				else if (eagerMatch(in, "initheur "))
				{
					if (eagerMatch(in, "fa"))
					{
						if (eagerMatch(in, "ctor"))
						{
#ifdef VAR_FACTOR_ENABLED
							int varNumber = parseInt(in) - 1;
							while (currentSolver->nVars() <= varNumber)
								currentSolver->newVar();

							double varFactor = parseDouble(in);
							currentSolver->setVariableFactor(varNumber, varFactor);
#else
							fprintf(stderr, "Warning: variable factor is diabled when compilation.\n");
#endif
						}
						else if (eagerMatch(in, "lse"))
						{
#ifdef VAR_PRIORITY_ENABLED
							int varNumber = parseInt(in) - 1;
							while (currentSolver->nVars() <= varNumber)
								currentSolver->newVar();

							int varPriority = parseInt(in);
							currentSolver->setVariablePriority(varNumber, varPriority);
							currentSolver->setUserDefinedPolarity(varNumber, false);
#else
							fprintf(stderr, "Warning: variable priority setting is diabled when compilation.\n");
#endif
						}
					}
					else if (eagerMatch(in, "init"))
					{
						int varNumber = parseInt(in) - 1;
						while (currentSolver->nVars() <= varNumber)
							currentSolver->newVar();

						double varBump = parseDouble(in);
						currentSolver->bumpVariableActivity(varNumber, varBump);
					}
					else if (eagerMatch(in, "level"))
					{
#ifdef VAR_PRIORITY_ENABLED
						int varNumber = parseInt(in) - 1;
						while (currentSolver->nVars() <= varNumber)
							currentSolver->newVar();

						int varPriority = parseInt(in);
						currentSolver->setVariablePriority(varNumber, varPriority);
#else
						fprintf(stderr, "Warning: variable priority setting is diabled when compilation.\n");
#endif
					}
					else if (eagerMatch(in, "sign"))
					{
						int varNumber = parseInt(in) - 1;
						while (currentSolver->nVars() <= varNumber)
							currentSolver->newVar();

						bool varPolarity = (parseInt(in) > 0);
						currentSolver->setUserDefinedPolarity(varNumber, varPolarity);
					}
					else if (eagerMatch(in, "true"))
					{
#ifdef VAR_PRIORITY_ENABLED
						int varNumber = parseInt(in) - 1;
						while (currentSolver->nVars() <= varNumber)
							currentSolver->newVar();

						int varPriority = parseInt(in);
						currentSolver->setVariablePriority(varNumber, varPriority);
						currentSolver->setUserDefinedPolarity(varNumber, true);
#else
						fprintf(stderr, "Warning: variable priority setting is diabled when compilation.\n");
#endif
					}
				}
				else if (eagerMatch(in, "config "))
				{
					if (eagerMatch(in, "c"))
					{
						if (eagerMatch(in, "la-decay="))
						{
							double clause_decay = parseDouble(in);
							if ((clause_decay <= 0) || (clause_decay >= 1))
								printf("PARSE ERROR! Clause decay value should be in the range 0 to 1, exclusive.\n"), exit(3);
							currentSolver->clause_decay = clause_decay;
						}
						else if (eagerMatch(in, "cmin-mode="))
						{
							int ccmin_mode = parseInt(in);
							if ((ccmin_mode < 0) || (ccmin_mode > 2))
								printf("PARSE ERROR! Conflict clause minimization value should be either 0, 1 or 2.\n"), exit(3);
							currentSolver->ccmin_mode = ccmin_mode;
						}
					}
					else if (eagerMatch(in, "early-prop="))
						currentSolver->early_propagation = parseBoolean(in);
					else if (eagerMatch(in, "gc-frac="))
					{
						double garbage_frac = parseDouble(in);
						if (garbage_frac <= 0)
							printf("PARSE ERROR! Garbage frac value should be greater than 0.\n"), exit(3);
						currentSolver->garbage_frac = garbage_frac;
					}
					else if (eagerMatch(in, "heavy-prop="))
						currentSolver->heavy_propagation = parseBoolean(in);
					else if (eagerMatch(in, "lazy-prop="))
						currentSolver->lazy_propagation = parseBoolean(in);
					else if (eagerMatch(in, "m"))
					{
						if (eagerMatch(in, "ax-confl-try="))
						{
							int max_confl_try = parseInt(in);
							if (max_confl_try <= 0)
								printf("PARSE ERROR! Maximum tries for conflict minimization should be greater than zero.\n"), exit(3);
							currentSolver->min_conflict_tries = max_confl_try;
						}
#ifndef GLUCOSE3
						else if (eagerMatch(in, "in-step-size="))
						{
							double min_step_size = parseDouble(in);
							if ((min_step_size <= 0) || (min_step_size >= 1))
								printf("PARSE ERROR! Minimum step size value should be in the range 0 to 1, exclusive.\n"), exit(3);
							currentSolver->min_step_size = min_step_size;
						}
#endif
					}
					else if (eagerMatch(in, "phase-saving="))
					{
						int phase_saving = parseInt(in);
						if ((phase_saving < 0) || (phase_saving > 2))
							printf("PARSE ERROR! Phase saving value should be either 0, 1, or 2.\n"), exit(3);
						currentSolver->phase_saving = phase_saving;
					}
					else if (eagerMatch(in, "r"))
					{
						if (eagerMatch(in, "first="))
						{
#ifndef GLUCOSE3
							int restart_first = parseInt(in);
							if (restart_first < 1)
								printf("PARSE ERROR! First restart value should be greater than 1.\n"), exit(3);
							currentSolver->restart_first = restart_first;
#endif
						}
#ifndef GLUCOSE3
						else if (eagerMatch(in, "inc="))
						{
							double restart_inc = parseDouble(in);
							if (restart_inc <= 1)
								printf("PARSE ERROR! Restart inc value should be greater than 1.\n"), exit(3);
							currentSolver->restart_inc = restart_inc;
						}
#endif
						else if (eagerMatch(in, "nd-"))
						{
							if (eagerMatch(in, "freq="))
							{
								double random_var_freq = parseDouble(in);
								if ((random_var_freq < 0) || (random_var_freq > 1))
									printf("PARSE ERROR! Random var frequency should be in the range 0 to 1, inclusive.\n"), exit(3);
								currentSolver->random_var_freq = random_var_freq;
							}
							else if (eagerMatch(in, "init="))
								currentSolver->rnd_init_act = parseBoolean(in);
							else if (eagerMatch(in, "pol="))
								currentSolver->rnd_pol = parseBoolean(in);
							else if (eagerMatch(in, "seed="))
							{
								double random_seed = parseDouble(in);
								if (random_seed <= 0)
									printf("PARSE ERROR! Random seed should be greater than 0.\n"), exit(3);
								currentSolver->random_seed = random_seed;
							}
						}
					}
#ifndef GLUCOSE3
					else if (eagerMatch(in, "step-size"))
					{
						if (eagerMatch(in, "="))
						{
							double step_size = parseDouble(in);
							if ((step_size <= 0) || (step_size >= 1))
								printf("PARSE ERROR! Step size value should be in the range 0 to 1, exclusive.\n"), exit(3);
							currentSolver->step_size = step_size;
						}
						else if (eagerMatch(in, "-dec="))
						{
							double step_size_dec = parseDouble(in);
							if ((step_size_dec <= 0) || (step_size_dec >= 1))
								printf("PARSE ERROR! Step size decrement value should be in the range 0 to 1, exclusive.\n"), exit(3);
							currentSolver->step_size_dec = step_size_dec;
						}
					}
#endif
					else if (eagerMatch(in, "var-decay="))
					{
						double var_decay = parseDouble(in);
						if ((var_decay <= 0) || (var_decay >= 1))
							printf("PARSE ERROR! Var decay value should be in the range 0 to 1, exclusive.\n"), exit(3);
						currentSolver->var_decay = var_decay;
					}
				}
			}
			skipLine(in);
		}
		else if (eagerMatch(in, "end"))
		{
			if (eagerMatch(in, "graph"))
			{
				if (!insideGraph)
					printf("PARSE ERROR! Endgraph keyword without a graph keyword\n"), exit(3);

				assert(graph);
				graph->createInverseArcs();
				insideGraph = false;
			}
			else if (eagerMatch(in, "module"))
			{
				if (!insideModule)
					printf("PARSE ERROR! Endmodule keyword wihout a module keyword\n"), exit(3);
				if (insideGraph)
					printf("PARSE ERROR! Endmodule keyword inside a graph\n"), exit(3);

				currentSolver = mainSolver;
				currentSolverVarCount = mainSolverVarCount;
				currentInputVarToIndexMap.clear();

				insideModule = false;
			}
			else
				printf("PARSE ERROR! Unknown keyword\n"), exit(3);
		}
		else if (eagerMatch(in, "falsify"))
		{ // a module should be falsified
			size_t moduleNo = parseInt(in), n;
			if ((moduleNo < 0) || (moduleNo >= modules.size()))
				printf("PARSE ERROR! Module number out of bound\n"), exit(3);
			else if (insideModule && (moduleNo == modules.size() - 1))
				printf("PARSE ERROR! Module refers to itself\n"), exit(3);
			Solver *internalSolver = modules[moduleNo].first;

			vector< pair<Var, Var> > lowerbounds;
			vector< pair<Var, Var> > upperbounds;
			const vector< pair<Var, Var> > &moduleInputVars = modules[moduleNo].second;
			n = modules[moduleNo].second.size(); // the number of input mappings that the module expects
			for (size_t i = 0; i < n; i++)
			{
				Var externalVar = parseInt(in) - 1;
				if (moduleInputVars[i].first >= 0)
					// should map the lowerbound of current external variable to the positive occurrences of the i-th input
					// since we want to falsify a module, positive occurrences inside module correspond to negative occurrences outside it
					lowerbounds.push_back(pair<Var, Var>(getMappedVar(externalVar, false), moduleInputVars[i].first));
				if (moduleInputVars[i].second >= 0)
					// should map the upperbound of current external variable to the negative occurrences of the i-th input
					// since we want to falsify a module, negative occurrences inside module correspond to positive occurrences outside it
					upperbounds.push_back(pair<Var, Var>(getMappedVar(externalVar, true), moduleInputVars[i].second));

				while (currentSolver->nVars() <= externalVar)
					currentSolver->newVar();
			}

			vector< pair<Lit, vector<Lit> > > reasonGenerator;
			TriggerProtectedPropagator *prop = new GeneralizedPropagator(currentSolver, internalSolver, true, currentSolverVarCount, internalSolver->nVars(), upperbounds, lowerbounds, reasonGenerator);
			currentSolver->addPropagator(prop);
		}
		else if (eagerMatch(in, "g"))
		{
			if (eagerMatch(in, "r"))
			{
				if (eagerMatch(in, "aph")) // graph keyword
				{
					if (insideGraph)
						printf("PARSE ERROR! One graph inside another graph\n"), exit(3);
					if (insideModule)
						printf("PARSE ERROR! Graph definition inside module is not currently supported\n"), exit(3);

					graph = new SATGraph();
					graph->createGraph(currentSolverVarCount);
					graph->initGraph(parseInt(in)+1);

					insideGraph = true;
				}
				else if (eagerMatch(in, "eachable")) // greachable keyword
				{
					if (insideGraph)
						printf("PARSE ERROR! Graph propagator defined inside a graph\n"), exit(3);
					if (graph == NULL)
						printf("PARSE ERROR! Graph propagator defined without defining a graph\n"), exit(3);
					if (insideModule)
						printf("PARSE ERROR! Graph propagator inside module is not currently supported\n"), exit(3);

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

					currentSolver->addPropagator(new GeneralizedReachabilityPropagator(currentSolver, currentSolverVarCount, graph, source, dests));
				}
				else if (eagerMatch(in, "nonreach")) // grnonreach keyword
				{
					if (insideGraph)
						printf("PARSE ERROR! Graph propagator defined inside a graph\n"), exit(3);
					if (graph == NULL)
						printf("PARSE ERROR! Graph propagator defined without defining a graph\n"), exit(3);
					if (insideModule)
						printf("PARSE ERROR! Graph propagator inside module is not currently supported\n"), exit(3);

					unordered_map<int, unordered_map<int, Lit> > reachabilities;
					int reachPairCount = parseInt(in);
					for (int i = 0; i < reachPairCount; i++)
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
					int nonreachPairCount = parseInt(in);
					for (int i = 0; i < nonreachPairCount; i++)
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

					currentSolver->addPropagator(new UnitReachabilityPropagator(currentSolver, graph, reachabilities, nonReachabilities));
				}
				else
					printf("PARSE ERROR! Unknown keyword\n"), exit(3);
			}
			else if (eagerMatch(in, "nonreach"))
			{
				if (insideGraph)
					printf("PARSE ERROR! Graph propagator defined inside a graph\n"), exit(3);
				if (graph == NULL)
					printf("PARSE ERROR! Graph propagator defined without defining a graph\n"), exit(3);
				if (insideModule)
					printf("PARSE ERROR! Graph propagator inside module is not currently supported\n"), exit(3);

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

				currentSolver->addPropagator(new GeneralizedNonreachabilityPropagator(currentSolver, currentSolverVarCount, graph, nodePairsList));
			}
			else
				printf("PARSE ERROR! Unknown keyword\n"), exit(3);
		}
		else if (eagerMatch(in, "m"))
		{
			if (eagerMatch(in, "inimize"))
			{
				if (insideGraph)
					printf("PARSE ERROR! Minimize keyword inside a graph\n"), exit(3);
				if (insideModule)
					printf("PARSE ERROR! Minimize keyword inside a module\n"), exit(3);

				int n = parseInt(in);
				while (n != 0)
				{
					Var var = getMappedVar(abs(n) - 1, n >= 0);
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
			else if (eagerMatch(in, "odule"))
			{
				if (insideGraph)
					printf("PARSE ERROR! Module keyword inside a graph\n"), exit(3);
				if (insideModule)
					printf("PARSE ERROR! Module keyword inside another module\n"), exit(3);

				currentSolver = Solver::newSolver();

				int n;
				currentSolverVarCount = parseInt(in);

				int moduleNo = modules.size();
				modules.push_back(pair<Solver *, vector< pair<Var, Var> > >(currentSolver, vector< pair<Var, Var> >()));
				assert(currentInputVarToIndexMap.size() == 0);

				n = parseInt(in); // the number input variables to the module
				for (int i = 0; i < n; i++)
				{
					Var v = parseInt(in) - 1;
					currentInputVarToIndexMap[v] = modules[moduleNo].second.size();
					modules[moduleNo].second.push_back(pair<Var, Var>(-1, -1));

					while (currentSolver->nVars() <= v)
						currentSolver->newVar();
				}

				insideModule = true;
			}
			else
				printf("PARSE ERROR! Unknown keyword\n"), exit(3);
		}
		else if (eagerMatch(in, "node"))
		{
			if (!insideGraph)
				printf("PARSE ERROR! Node keyword outside a graph\n"), exit(3);

			assert(graph);
			int n = parseInt(in);
			int a = parseInt(in);
			graph->createNode(n,a);
		}
		else if (*in == 'p')
		{
			if (eagerMatch(in, "p "))
			{
				if (eagerMatch(in, "cnf"))
				{
					mainSolverVarCount = currentSolverVarCount = parseInt(in);
					parseInt(in); // ignore clause count
				}
				else if (eagerMatch(in, "sts"))
					mainSolverVarCount = currentSolverVarCount = parseInt(in);
				else
					printf("PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
			}
			else
				printf("PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
		}
		else if (eagerMatch(in, "reachable"))
		{
			if (insideGraph)
				printf("PARSE ERROR! Graph propagator defined inside a graph\n"), exit(3);
			if (graph == NULL)
				printf("PARSE ERROR! Graph propagator defined without defining a graph\n"), exit(3);

			assert(graph);
			int source = parseInt(in);
			int destCount = parseInt(in);

			std::unordered_set<int> dests;
			for (int i = 0; i < destCount; i++)
				dests.insert(parseInt(in));

			currentSolver->addPropagator(new ReachabilityPropagator(currentSolver, currentSolverVarCount, graph, source, dests));
		}
		else if (eagerMatch(in, "satisfy")) // "satisfy" keyword found
		{
			printf("ERROR! Positive module call not implemented yet\n"), exit(3);
		}
		else // read a clause
		{
			int parsed_lit, var;

			lits.clear();
			for (;;)
			{
				parsed_lit = parseInt(in);
				if (parsed_lit == 0)
					break;

				var = getMappedVar(abs(parsed_lit) - 1, parsed_lit >= 0);
				while (var >= currentSolver->nVars())
					currentSolver->newVar();

				lits.push((parsed_lit >= 0) ? mkLit(var) : ~mkLit(var));
			}

			currentSolver->addClause_(lits);
			if (!insideModule)
				mxsolver->addHardClause(lits);
		}
	}

	if (insideGraph)
		printf("PARSE ERROR! File ended inside a graph\n"), exit(3);
	if (insideModule)
		printf("PARSE ERROR! File ended inside a module\n"), exit(3);

	mxsolver->initialize();
}

// Inserts problem into solver.
//
template<class Solver>
static void parse_STS(gzFile input_stream, Solver& S)
{
	StreamBuffer in(input_stream);
	parse_STS_main(in, S);
}

//=================================================================================================
}

#endif
