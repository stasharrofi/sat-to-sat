/*****************************************************************************************[MaxSAT.cc]
Open-WBO -- Copyright (c) 2013-2015, Ruben Martins, Vasco Manquinho, Ines Lynce

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
************************************************************************************************/

#include "maxsat/MaxSAT.h"
#include "maxsat/algorithms/Alg_incWBO.h"
#include "maxsat/algorithms/Alg_LinearSU.h"
#include "maxsat/algorithms/Alg_LinearUS.h"
#include "maxsat/algorithms/Alg_MSU3.h"
#include "maxsat/algorithms/Alg_WBO.h"
#include "maxsat/algorithms/Alg_WMSU3.h"
#include <iostream>

static const char* _maxsat = "MaxSAT";
static const char* _maxsat_encoding = "MaxSAT::Encoding";
static const char* _maxsat_wbo = "MaxSAT::WBO";

static IntOption algorithm(_maxsat, "algorithm", "Search algorithm (0=wbo, 1=linear-su, 2=linear-us, 3=msu3, 4=wmsu3, 5=best).\n", 5, IntRange(0, 5));
static IntOption incremental(_maxsat, "incremental", "Incremental level (0=none, 1=blocking, 2=weakening, 3=iterative) (only for unsat-based algorithms).\n", 3, IntRange(0, 3));
static BoolOption bmo(_maxsat, "bmo", "BMO search.\n", true);

static IntOption cardinality(_maxsat_encoding, "cardinality", "Cardinality encoding (0=cardinality networks, 1=totalizer, 2=modulo totalizer).\n", 1, IntRange(0, 2));
static IntOption amo(_maxsat_encoding, "amo", "AMO encoding (0=Ladder).\n", 0, IntRange(0, 0));
static IntOption pb(_maxsat_encoding, "pb", "PB encoding (0=SWC).\n", 0, IntRange(0, 0));

static IntOption weight(_maxsat_wbo, "weight-strategy", "Weight strategy (0=none, 1=weight-based, 2=diversity-based).\n", 2, IntRange(0, 2));
static BoolOption symmetry(_maxsat_wbo, "symmetry", "Symmetry breaking.\n", true);
static IntOption symmetry_lim(_maxsat_wbo, "symmetry-limit", "Limit on the number of symmetry breaking clauses.\n", 500000, IntRange(0, INT32_MAX));

using namespace NSPACE;

/************************************************************************************************
 //
 // Public methods
 //
 ************************************************************************************************/

void MaxSAT::search()
{
  printf("Error: Invalid MaxSAT algoritm.\n");
  exit(_ERROR_);
}

int MaxSAT::nVars()
{
  return nbVars;
} // Returns the number of variables in the working MaxSAT formula.
int MaxSAT::nSoft()
{
  return nbSoft;
} // Returns the number of soft clauses in the working MaxSAT formula.
int MaxSAT::nHard()
{
  return hardClauses.size();
} // Returns the number of hard clauses in the working MaxSAT formula.
void MaxSAT::newVar()
{
  nbVars++;
} // Increases the number of variables in the working MaxSAT formula.

// Adds a new hard clause to the hard clause database.
void MaxSAT::addHardClause(vec<Lit> &lits)
{
  hardClauses.push();
  new (&hardClauses[hardClauses.size() - 1]) Hard(lits);
  nbHard++;
}

// Adds a new soft clause to the hard clause database.
void MaxSAT::addSoftClause(int weight, vec<Lit> &lits)
{
	if (weight > 1)
		problemType = _WEIGHTED_;
  softClauses.push();
  vec<Lit> rVars;
  Lit assump = lit_Undef;

  new (&softClauses[softClauses.size() - 1]) Soft(lits, weight, assump, rVars);
  nbSoft++;
}

// Adds a new soft clause to the hard clause database with predefined relaxation
// variables.
void MaxSAT::addSoftClause(int weight, vec<Lit> &lits, vec<Lit> &vars)
{
  softClauses.push();
  Lit assump = lit_Undef;

  new (&softClauses[softClauses.size() - 1]) Soft(lits, weight, assump, vars);
  nbSoft++;
}

// Makes a new literal to be used in the working MaxSAT formula.
Lit MaxSAT::newLiteral(bool sign)
{
  Lit p = mkLit(nVars(), sign);
  newVar();
  return p;
}

void MaxSAT::setProblemType(int type)
{
  problemType = type;
} // Sets the problem type.
int MaxSAT::getProblemType() { return problemType; } // Return the problem type.

void MaxSAT::setProblemOptType(int optType)
{
  problemOptType = optType;
} // Sets the problem type.
int MaxSAT::getProblemOptType() { return problemOptType; } // Return the problem type.

// 'ubCost' is initialized to the sum of weights of the soft clauses.
void MaxSAT::updateSumWeights(int weight)
{
  if (weight != hardWeight) ubCost += weight;
}

// The initial 'currentWeight' corresponds to the maximum weight of the soft
// clauses.
void MaxSAT::setCurrentWeight(int weight)
{
  if (weight > currentWeight && weight != hardWeight) currentWeight = weight;
}
int MaxSAT::getCurrentWeight() { return currentWeight; }

void MaxSAT::setHardWeight(int weight)
{
  hardWeight = weight;
} // Sets the weight of hard clauses.
void MaxSAT::setInitialTime(double initial)
{
  initialTime = initial;
} // Sets the initial time.

void MaxSAT::copySolver(MaxSAT *solver)
{
	while (nVars() >= solver->nVars())
		solver->newVar();

	for (int i = 0; i < softClauses.size(); i++)
		solver->addSoftClause(softClauses[i].weight, softClauses[i].clause, softClauses[i].relaxationVars);

	for (int i = 0; i < hardClauses.size(); i++)
		solver->addHardClause(hardClauses[i].clause);

#ifdef SIMP
	solver->prototypeSolver = new SimpSolver((SimpSolver *) prototypeSolver);
#else
	solver->prototypeSolver = new Solver(prototypeSolver);
#endif

	solver->setProblemType(getProblemType());
	solver->setCurrentWeight(getCurrentWeight());
	solver->setHardWeight(hardWeight);
	solver->ubCost = ubCost;
	solver->lbCost = lbCost;

	solver->nbSatisfiable = nbSatisfiable;
	solver->nbCores = nbCores;

	//solver->nbInitialVariables = nbInitialVariables;
	//if (nbInitialVariables != 0) solver->saveModel(model);

	solver->initialTime = initialTime;
}

/************************************************************************************************
 //
 // SAT solver interface -- simplifying the 'simp' or 'core' use of the SAT
 solver
 //
 ************************************************************************************************/

// Creates an empty SAT Solver.
Solver *MaxSAT::newSATSolver()
{
#ifdef SIMP
  SimpSolver *S = new SimpSolver((SimpSolver *) prototypeSolver);
#else
  Solver *S = new Solver(prototypeSolver);
#endif

  return (Solver *)S;
}

// Creates a new variable in the SAT solver.
void MaxSAT::newSATVariable(Solver *S)
{
	S->newVar();
}

// Solve the formula that is currently loaded in the SAT solver with a set of
// assumptions and with the option to use preprocessing for 'simp'.
lbool MaxSAT::searchSATSolver(Solver *S, vec<Lit> &assumptions, bool pre)
{

// Currently preprocessing is disabled by default.
// Variable elimination cannot be done on relaxation variables nor on variables
// that belong to soft clauses. To preprocessing to be used those variables
// should be frozen.

#ifdef SIMP
  lbool res = ((SimpSolver *)S)->solveLimited(assumptions, pre);
#else
  lbool res = S->solveLimited(assumptions);
#endif

  return res;
}

// Solve the formula without assumptions.
lbool MaxSAT::searchSATSolver(Solver *S, bool pre)
{
  vec<Lit> dummy; // Empty set of assumptions.
  return searchSATSolver(S, dummy, pre);
}

/************************************************************************************************
 //
 // Utils for model management
 //
 ************************************************************************************************/

/*_________________________________________________________________________________________________
  |
  |  saveModel : (currentModel : vec<lbool>&)  ->  [void]
  |
  |  Description:
  |
  |    Saves the current model found by the SAT solver.
  |
  |  Pre-conditions:
  |    * Assumes that 'nbInitialVariables' has been initialized.
  |    * Assumes that 'currentModel' is not empty.
  |
  |  Post-conditions:
  |    * 'model' is updated to the current model.
  |
  |________________________________________________________________________________________________@*/
void MaxSAT::saveModel(vec<lbool> &currentModel)
{
  assert(prototypeSolver->nVars() != 0);
  assert(currentModel.size() != 0);

  model.clear();
  // Only store the value of the variables that belong to the
  // original MaxSAT formula.
  for (int i = 0; i < prototypeSolver->nVars(); i++)
    model.push(currentModel[i]);
}

/*_________________________________________________________________________________________________
  |
  |  computeCostModel : (currentModel : vec<lbool>&) (weight : int) ->
  |                     [uint64_t]
  |
  |  Description:
  |
  |    Computes the cost of 'currentModel'. The cost of a model is the sum of
  |    the weights of the unsatisfied soft clauses.
  |    If a weight is specified, then it only considers the sum of the weights
  |    of the unsatisfied soft clauses with the specified weight.
  |
  |  Pre-conditions:
  |    * Assumes that 'currentModel' is not empty.
  |
  |________________________________________________________________________________________________@*/
uint64_t MaxSAT::computeCostModel(vec<lbool> &currentModel, int weight)
{

  assert(currentModel.size() != 0);
  uint64_t currentCost = 0;

  for (int i = 0; i < nSoft(); i++)
  {
    bool unsatisfied = true;
    for (int j = 0; j < softClauses[i].clause.size(); j++)
    {

      if (weight != INT32_MAX && softClauses[i].weight != weight)
      {
        unsatisfied = false;
        continue;
      }

      assert(var(softClauses[i].clause[j]) < currentModel.size());
      if ((sign(softClauses[i].clause[j]) &&
           currentModel[var(softClauses[i].clause[j])] == l_False) ||
          (!sign(softClauses[i].clause[j]) &&
           currentModel[var(softClauses[i].clause[j])] == l_True))
      {
        unsatisfied = false;
        break;
      }
    }

    if (unsatisfied) currentCost += softClauses[i].weight;
  }

  return currentCost;
}

/*_________________________________________________________________________________________________
  |
  |  isBMO : (cache : bool)  ->  [void]
  |
  |  Description:
  |
  |    Tests if the MaxSAT formula has lexicographical optimization criterion.
  |
  |  For further details see:
  |    * Joao Marques-Silva, Josep Argelich, Ana Graça, Inês Lynce: Boolean
  |      lexicographic optimization: algorithms & applications. Ann. Math.
  |      Artif. Intell. 62(3-4): 317-343 (2011)
  |
  |  Post-conditions:
  |    * 'orderWeights' is updated with the weights in lexicographical order if
  |      'cache' is true.
  |
  |________________________________________________________________________________________________@*/
bool MaxSAT::isBMO(bool cache)
{
  assert (orderWeights.size() == 0);
  bool bmo = true;
  std::set<int> partitionWeights;
  std::map<int, int> nbPartitionWeights;

  for (int i = 0; i < nSoft(); i++)
  {
    partitionWeights.insert(softClauses[i].weight);
    nbPartitionWeights[softClauses[i].weight]++;
  }

  for (std::set<int>::iterator iter = partitionWeights.begin();
       iter != partitionWeights.end(); ++iter)
  {
    orderWeights.push_back(*iter);
  }

  std::sort(orderWeights.begin(), orderWeights.end(), greaterThan);

  uint64_t totalWeights = 0;
  for (int i = 0; i < (int)orderWeights.size(); i++)
    totalWeights += orderWeights[i] * nbPartitionWeights[orderWeights[i]];

  for (int i = 0; i < (int)orderWeights.size(); i++)
  {
    totalWeights -= orderWeights[i] * nbPartitionWeights[orderWeights[i]];
    if (orderWeights[i] < totalWeights)
    {
      bmo = false;
      break;
    }
  }

  if (!cache) orderWeights.clear();

  return bmo;
}

/************************************************************************************************
 //
 // Utils for printing
 //
 ************************************************************************************************/

// Prints information regarding the incremental configuration.
void MaxSAT::print_Incremental_configuration(int incremental)
{
	if (verbosity > 0)
	{
		switch (incremental)
		{
			case _INCREMENTAL_NONE_:
				printf("c |  Incremental Strategy: %12s                                "
				       "                                   |\n",
				       "None");
				break;
			case _INCREMENTAL_BLOCKING_:
				printf("c |  Incremental Strategy: %12s                                "
				       "                                   |\n",
				       "Blocking");
				break;
			case _INCREMENTAL_WEAKENING_:
				printf("c |  Incremental Strategy: %12s                                "
				       "                                   |\n",
				       "Weakening");
				break;
			case _INCREMENTAL_ITERATIVE_:
				printf("c |  Incremental Strategy:    %s                               "
				       "                           |\n",
				       "Iterative Encoding");
				break;
			default:
				printf("c Error: Invalid incremental strategy.\n");
				printf("c UNKNOWN\n");
				exit(_ERROR_);
		}
	}
}

// Prints information regarding the AMO encoding.
void MaxSAT::print_AMO_configuration(int encoding)
{
	if (verbosity > 0)
	{
		switch (encoding)
		{
			case _AMO_LADDER_:
				printf("c |  AMO Encoding:         %12s                      "
				       "                                             |\n",
				       "Ladder");
				break;

			default:
				printf("c Error: Invalid AMO encoding.\n");
				printf("c UNKNOWN\n");
				break;
		}
	}
}

// Prints information regarding the PB encoding.
void MaxSAT::print_PB_configuration(int encoding)
{
	if (verbosity > 0)
	{
		switch (encoding)
		{
			case _PB_SWC_:
				printf("c |  PB Encoding:         %13s                        "
				       "                                           |\n",
				       "SWC");
				break;

			default:
				printf("c Error: Invalid PB encoding.\n");
				printf("c UNKNOWN\n");
				break;
		}
	}
}

// Prints information regarding the cardinality encoding.
void MaxSAT::print_Card_configuration(int encoding)
{
	if (verbosity > 0)
	{
		switch (encoding)
		{
			case _CARD_CNETWORKS_:
				printf("c |  Cardinality Encoding: %12s                                "
				       "                                   |\n",
				       "CNetworks");
				break;

			case _CARD_TOTALIZER_:
				printf("c |  Cardinality Encoding: %12s                                "
				       "                                   |\n",
				       "Totalizer");
				break;

			case _CARD_MTOTALIZER_:
				printf("c |  Cardinality Encoding:    %19s                             "
				       "                            |\n",
				       "Modulo Totalizer");
				break;

			default:
				printf("c Error: Invalid cardinality encoding.\n");
				printf("c UNKNOWN\n");
				break;
		}
	}
}

// Prints the best satisfying model. Assumes that 'model' is not empty.
void MaxSAT::printModel()
{
	assert(model.size() != 0);

	if (prototypeSolver->getModelPrintingMethod() == 1)
	{ // Print model in ASP way.
		printf("ANSWER\n");
		for (int i = 0; i < model.size(); i++)
			if (model[i] == l_True)
			{
				const char *s = prototypeSolver->getVariableName(i);
				if (s != NULL)
					if (prototypeSolver->getShowExternalVariables() || ((*s) && (*s != '_')))
						std::cout << s << ". ";
			}
		printf("\n");
		if (nSoft() > 0)
			printf("COST %" PRIu64 "@0\n", computeCostModel(model));
	}
	else
	{ // Print model in SAT way.
		printf("v ");
		for (int i = 0; i < model.size(); i++)
		{
			if (model[i] == l_True)
				printf("%d ", i + 1);
			else
				printf("%d ", -(i + 1));
		}
		printf("\n");
	}
}

// Prints search statistics.
void MaxSAT::printStats()
{
	if (verbosity > 0)
	{
		double totalTime = cpuTime();
		float avgCoreSize = 0;
		if (nbCores != 0) avgCoreSize = (float)sumSizeCores / nbCores;

		printf("c\n");
		if (nSoft() > 0)
			if (model.size() == 0)
				printf("c  Best solution:          %12s\n", "-");
			else
				printf("c  Best solution:          %12" PRIu64 "\n", ubCost);
		printf("c  Total time:             %12.2f s\n", totalTime - initialTime);
		if (nSoft() > 0)
		{
			printf("c  Nb SAT calls:           %12d\n", nbSatisfiable);
			printf("c  Nb UNSAT calls:         %12d\n", nbCores);
			printf("c  Average core size:      %12.2f\n", avgCoreSize);
		}
		printf("c  Nb symmetry clauses:    %12d\n", nbSymmetryClauses);
		printf("c\n");
	}
}

// Prints the corresponding answer.
void MaxSAT::printAnswerAndExit(int type)
{
	if (verbosity > 0) printStats();

	if (type == _UNKNOWN_ && model.size() > 0) type = _SATISFIABLE_;
	if (type == _OPTIMUM_ && nSoft() == 0) type = _SATISFIABLE_;

	switch (type)
	{
		case _SATISFIABLE_:
			if (prototypeSolver->getModelPrintingMethod() == 0) // Output in SAT format
				printf("s SATISFIABLE\n");
			printModel();
			break;
		case _OPTIMUM_:
			if (prototypeSolver->getModelPrintingMethod() == 0) // Output in SAT format
				printf("s OPTIMUM FOUND\n");
			printModel();
			if (prototypeSolver->getModelPrintingMethod() == 1) // Output in ASP format
				printf("OPTIMUM\n");
			break;
		case _UNSATISFIABLE_:
			if (prototypeSolver->getModelPrintingMethod() == 0) // Output in SAT format
				printf("s UNSATISFIABLE\n");
			else if (prototypeSolver->getModelPrintingMethod() == 1) // Output in ASP format
				printf("INCONSISTENT");
			break;
		case _UNKNOWN_:
			printf("s UNKNOWN\n");
			break;
		default:
			printf("c Error: Invalid answer type.\n");
	}

	if (prototypeSolver->getModelPrintingMethod() == 0) // Exit codes according to SAT standard
		_exit(type);
	else if (prototypeSolver->getModelPrintingMethod() == 1) // Exit codes according to ASP standard
	{
		if (type == _UNKNOWN_)
			_exit(1); // In ASP standard, UNKNOWN exit code is 1 (instead of 40 in SAT standard)
		else
			_exit(type);
	}
	else
		_exit(1); // Wrong model printing method
}

MaxSAT *MaxSAT::create(double initial_time, int verbosity)
{
	MaxSAT *S = NULL;

	switch ((int) algorithm)
	{
		case _ALGORITHM_WBO_:
			if (incremental == _INCREMENTAL_NONE_)
				S = new WBO(verbosity, weight, symmetry, symmetry_lim);
			else if (incremental == _INCREMENTAL_BLOCKING_)
				S = new incWBO(verbosity, weight, symmetry, symmetry_lim, amo);
			else
			{
				printf("c Error: WBO algorithm only supports blocking incrementality.\n");
				printf("c UNKNOWN\n");
				exit(_ERROR_);
			}
			break;

		case _ALGORITHM_LINEAR_SU_:
			S = new LinearSU(verbosity, bmo, cardinality, pb);
			break;

		case _ALGORITHM_LINEAR_US_:
			S = new LinearUS(verbosity, incremental, cardinality);
			break;

		case _ALGORITHM_MSU3_:
			S = new MSU3(verbosity, incremental, cardinality);
			break;

		case _ALGORITHM_WMSU3_:
			S = new WMSU3(verbosity, incremental, cardinality, pb, bmo);
			break;

		case _ALGORITHM_BEST_:
			S = new MSU3(verbosity, _INCREMENTAL_ITERATIVE_, _CARD_TOTALIZER_);
			break;

		default:
			printf("c Error: Invalid MaxSAT algorithm.\n");
			printf("c UNKNOWN\n");
			exit(_ERROR_);
	}

	S->setInitialTime(initial_time);

	return S;
}

MaxSAT *MaxSAT::recreate(MaxSAT *S)
{
	if (algorithm == _ALGORITHM_BEST_ && S->getProblemType() == _WEIGHTED_)
	{
		// Check if the formula is BMO without caching the bmo functions.
		bool bmo_strategy = S->isBMO(false);
		MaxSAT *solver;
		if (bmo_strategy)
			solver = new WMSU3(S->verbosity, _INCREMENTAL_ITERATIVE_, _CARD_TOTALIZER_, _PB_SWC_, true);
		else
			solver = new WBO(S->verbosity, _WEIGHT_DIVERSIFY_, true, 500000);

		// HACK: Copy the contents of a solver to a fresh solver.
		// This could be avoided if the parsing was done to a DB that is
		// independent from the solver.
		S->copySolver(solver);
		delete S;
		return solver;
	}
	else
		return S;
}
