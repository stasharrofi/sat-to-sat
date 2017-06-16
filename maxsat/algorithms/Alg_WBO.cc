/*****************************************************************************************[Alg_WBO.cc]
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

#include "Alg_WBO.h"

using namespace NSPACE;

/************************************************************************************************
 //
 // Rebuild MaxSAT solver
 //
 ************************************************************************************************/

/*_________________________________________________________________________________________________
  |
  |  rebuildWeightSolver : (strategy : int)  ->  [Solver *]
  |
  |   Description:
  |
  |    Rebuilds a SAT solver with the current MaxSAT formula using a
  |    weight-based strategy.
  |    Only soft clauses with weight greater or equal to 'currentWeight' are
  |    considered in the working MaxSAT formula.
  |
  |   For further details see:
  |     * Ruben Martins, Vasco Manquinho, Ines Lynce: On Partitioning for
  |       Maximum Satisfiability. ECAI 2012: 913-914
  |	    * Carlos Ansótegui, Maria Luisa Bonet, Joel Gabàs, Jordi Levy:
  |       Improving SAT-Based Weighted MaxSAT Solvers. CP 2012: 86-101
  |
  |   Pre-conditions:
  |     * Assumes that 'currentWeight' has been previously updated.
  |     * Assumes that the weight strategy is either '_WEIGHT_NORMAL_' or
  |       '_WEIGHT_DIVERSIFY_'.
  |
  |   Post-conditions:
  |     * 'nbCurrentSoft' is updated to the number of soft clauses in the
  |        working MaxSAT formula.
  |
  |________________________________________________________________________________________________@*/
Solver *WBO::rebuildWeightSolver(int strategy)
{

  assert(strategy == _WEIGHT_NORMAL_ || strategy == _WEIGHT_DIVERSIFY_);

  Solver *S = newSATSolver();

  for (int i = 0; i < nVars(); i++)
    newSATVariable(S);

  for (int i = 0; i < nHard(); i++)
    S->addClause(hardClauses[i].clause);

  if (symmetryStrategy) symmetryBreaking();

  vec<Lit> clause;
  nbCurrentSoft = 0;
  for (int i = 0; i < nSoft(); i++)
  {
    if (softClauses[i].weight >= currentWeight)
    {
      nbCurrentSoft++;
      clause.clear();
      softClauses[i].clause.copyTo(clause);
      for (int j = 0; j < softClauses[i].relaxationVars.size(); j++)
        clause.push(softClauses[i].relaxationVars[j]);
      clause.push(softClauses[i].assumptionVar);

      S->addClause(clause);
    }
  }

  return S;
}

/*_________________________________________________________________________________________________
  |
  |  rebuildSolver : [void]  ->  [Solver *]
  |
  |  Description:
  |
  |    Rebuilds a SAT solver with the current MaxSAT formula using the original
  |    WBO strategy.
  |    All soft clauses are considered in the working formula.
  |
  |  Pre-conditions:
  |    * Assumes that the weight strategy is '_WEIGHT_NONE_'.
  |
  |________________________________________________________________________________________________@*/
Solver *WBO::rebuildSolver()
{

  assert(weightStrategy == _WEIGHT_NONE_);

  Solver *S = newSATSolver();

  for (int i = 0; i < nVars(); i++)
    newSATVariable(S);

  for (int i = 0; i < nHard(); i++)
    S->addClause(hardClauses[i].clause);

  if (symmetryStrategy) symmetryBreaking();

  vec<Lit> clause;
  for (int i = 0; i < nSoft(); i++)
  {
    clause.clear();
    softClauses[i].clause.copyTo(clause);
    for (int j = 0; j < softClauses[i].relaxationVars.size(); j++)
      clause.push(softClauses[i].relaxationVars[j]);
    clause.push(softClauses[i].assumptionVar);

    S->addClause(clause);
  }
  return S;
}

/*_________________________________________________________________________________________________
  |
  |  rebuildHardSolver : [void]  ->  [Solver *]
  |
  |  Description:
  |
  |    Rebuilds a SAT solver with the hard clauses of the MaxSAT formula.
  |    Used for testing if the MaxSAT formula is unsatisfiable.
  |
  |________________________________________________________________________________________________@*/
Solver *WBO::rebuildHardSolver()
{

  Solver *S = newSATSolver();

  for (int i = 0; i < nVars(); i++)
    newSATVariable(S);

  for (int i = 0; i < nHard(); i++)
    S->addClause(hardClauses[i].clause);

  return S;
}

/*_________________________________________________________________________________________________
  |
  |  updateCurrentWeight : (strategy : int)  ->  [void]
  |
  |  Description:
  |
  |    Updates the value of 'currentWeight' with a predefined strategy.
  |
  |  Pre-conditions:
  |    * Assumes that the weight strategy is either '_WEIGHT_NORMAL_' or
  |      '_WEIGHT_DIVERSIFY_'.
  |
  |  Post-conditions:
  |    * 'currentWeight' is updated by this method.
  |
  |________________________________________________________________________________________________@*/
void WBO::updateCurrentWeight(int strategy)
{

  assert(strategy == _WEIGHT_NORMAL_ || strategy == _WEIGHT_DIVERSIFY_);

  if (strategy == _WEIGHT_NORMAL_)
    currentWeight = findNextWeight(currentWeight);
  else if (strategy == _WEIGHT_DIVERSIFY_)
    currentWeight = findNextWeightDiversity(currentWeight);
}

/*_________________________________________________________________________________________________
  |
  |  findNextWeight : (weight : int)  ->  [int]
  |
  |  Description:
  |
  |    Finds the greatest weight that is smaller than the 'currentWeight'.
  |
  |  For further details see:
  |    * Ruben Martins, Vasco Manquinho, Ines Lynce: On Partitioning for Maximum
  |      Satisfiability. ECAI 2012: 913-914
  |
  |________________________________________________________________________________________________@*/
int WBO::findNextWeight(int weight)
{

  int nextWeight = 1;
  for (int i = 0; i < nSoft(); i++)
  {
    if (softClauses[i].weight > nextWeight && softClauses[i].weight < weight)
      nextWeight = softClauses[i].weight;
  }

  return nextWeight;
}

/*_________________________________________________________________________________________________
  |
  |  findNextWeightDiversity : (weight : int)  ->  [int]
  |
  |  Description:
  |
  |  Finds the greatest weight that is smaller than the 'currentWeight' and
  |  respects a given ratio
  |  between the number of different weights and the number of soft clauses.
  |
  |  Pre-conditions:
  |    * Assumes that the weight strategy is '_WEIGHT_DIVERSIFY_'.
  |    * Assumes that 'unsatSearch' was call before (this implies that
  |      nbSatisfable > 0).
  |
  |  For further details see:
  |    * Carlos Ansótegui, Maria Luisa Bonet, Joel Gabàs, Jordi Levy: Improving
  |      SAT-Based Weighted MaxSAT Solvers. CP 2012: 86-101
  |
  |________________________________________________________________________________________________@*/
int WBO::findNextWeightDiversity(int weight)
{

  assert(weightStrategy == _WEIGHT_DIVERSIFY_);
  assert(nbSatisfiable > 0); // Assumes that unsatSearch was done before.

  int nextWeight = weight;
  int nbClauses = 0;
  std::set<int64_t> nbWeights;
  float alpha = 1.25;

  bool findNext = false;

  for (;;)
  {
    if (nbSatisfiable > 1 || findNext) nextWeight = findNextWeight(nextWeight);

    nbClauses = 0;
    nbWeights.clear();
    for (int i = 0; i < nSoft(); i++)
    {
      if (softClauses[i].weight >= nextWeight)
      {
        nbClauses++;
        nbWeights.insert(softClauses[i].weight);
      }
    }

    if ((float)nbClauses / nbWeights.size() > alpha || nbClauses == nSoft())
      break;

    if (nbSatisfiable == 1 && !findNext) findNext = true;
  }

  return nextWeight;
}

/************************************************************************************************
 //
 // Utils for core management
 //
 ************************************************************************************************/

/*_________________________________________________________________________________________________
  |
  |  encodeEO : (lits : vec<Lit>&)  ->  [void]
  |
  |  Description:
  |
  |    Encodes that exactly one literal from 'lits' is assigned value true.
  |    Uses the Ladder/Regular encoding for translating the EO constraint into
  |    CNF.
  |    NOTE: We do not use the 'encoder' since we are adding clauses to the hard
  |    clauses and not directly into the SAT solvers.
  |    If a different AMO is used, then this method should be changed
  |    accordingly.
  |
  |  For further details see:
  |    * Carlos Ansótegui, Felip Manyà: Mapping Problems with Finite-Domain
  |      Variables into Problems with Boolean Variables. SAT 2004
  |    * Ian Gent and Peter Nightingale. A New Encoding of All Different into
  |      SAT. ModRef 2004
  |
  |  Pre-conditions:
  |    * Assumes that 'lits' is not empty.
  |
  |  Post-conditions:
  |    * 'hardClauses' are updated with the clauses that encode the EO
  |      constraint.
  |
  |________________________________________________________________________________________________@*/
void WBO::encodeEO(vec<Lit> &lits)
{

  assert(lits.size() != 0);

  vec<Lit> clause;
  if (lits.size() == 1)
  {
    clause.push(lits[0]);
    addHardClause(clause);
  }
  else
  {

    vec<Lit> auxVariables;

    for (int i = 0; i < lits.size() - 1; i++)
    {
      Lit p = newLiteral();
      auxVariables.push(p);
    }

    for (int i = 0; i < lits.size(); i++)
    {
      if (i == 0)
      {
        clause.clear();
        clause.push(lits[i]);
        clause.push(~auxVariables[i]);
        addHardClause(clause);
        clause.clear();
        clause.push(~lits[i]);
        clause.push(auxVariables[i]);
        addHardClause(clause);
      }
      else if (i == lits.size() - 1)
      {
        clause.clear();
        clause.push(lits[i]);
        clause.push(auxVariables[i - 1]);
        addHardClause(clause);
        clause.clear();
        clause.push(~lits[i]);
        clause.push(~auxVariables[i - 1]);
        addHardClause(clause);
      }
      else
      {
        clause.clear();
        clause.push(~auxVariables[i - 1]);
        clause.push(auxVariables[i]);
        addHardClause(clause);
        clause.clear();
        clause.push(lits[i]);
        clause.push(~auxVariables[i]);
        clause.push(auxVariables[i - 1]);
        addHardClause(clause);
        clause.clear();
        clause.push(~lits[i]);
        clause.push(auxVariables[i]);
        addHardClause(clause);
        clause.clear();
        clause.push(~lits[i]);
        clause.push(~auxVariables[i - 1]);
        addHardClause(clause);
      }
    }
  }
}

/*_________________________________________________________________________________________________
  |
  |  relaxCore : (conflict : vec<Lit>&) (weightCore : int) (assumps : vec<Lit>&)
  |              ->  [void]
  |
  |  Description:
  |
  |    Relaxes the core as described in the original WBO paper.
  |
  |  For further details see:
  |    * Vasco Manquinho, Joao Marques-Silva, Jordi Planes: Algorithms for
  |      Weighted Boolean Optimization. SAT 2009: 495-508
  |
  |  Pre-conditions:
  |    * Assumes that the core ('conflict') is not empty.
  |    * Assumes that the weight of the core is not 0 (should always be greater
  |      than or equal to 1).
  |
  |  Post-conditions:
  |    * If the weight of the soft clause is the same as the weight of the core:
  |      - 'softClauses[indexSoft].relaxationVars' is updated with a new
  |        relaxation variable.
  |    * If the weight of the soft clause is not the same as the weight of the
  |      core:
  |      - 'softClauses[indexSoft].weight' is decreased by the weight of the
  |        core.
  |      - A new soft clause is created. This soft clause has the weight of the
  |        core.
  |      - A new assumption literal is created and attached to the new soft
  |        clause.
  |      - 'coreMapping' is updated to map the new soft clause to its assumption
  |        literal.
  |    * 'sumSizeCores' is updated.
  |
  |________________________________________________________________________________________________@*/
void WBO::relaxCore(vec<Lit> &conflict, int weightCore, vec<Lit> &assumps)
{

  assert(conflict.size() > 0);
  assert(weightCore > 0);

  vec<Lit> lits;

  for (int i = 0; i < conflict.size(); i++)
  {
    int indexSoft = coreMapping[conflict[i]];

    if (softClauses[indexSoft].weight == weightCore)
    {
      // If the weight of the soft clause is the same as the weight of the core
      // then relax it.
      Lit p = newLiteral();
      softClauses[indexSoft].relaxationVars.push(p);
      lits.push(p);

      if (symmetryStrategy) symmetryLog(indexSoft);
    }
    else
    {
      // If the weight of the soft clause is different from the weight of the
      // core then duplicate the soft clause.
      assert(softClauses[indexSoft].weight - weightCore > 0);
      // Update the weight of the soft clause.
      softClauses[indexSoft].weight -= weightCore;

      vec<Lit> clause;
      softClauses[indexSoft].clause.copyTo(clause);
      vec<Lit> vars;
      softClauses[indexSoft].relaxationVars.copyTo(vars);

      Lit p = newLiteral();
      vars.push(p);
      lits.push(p);

      // Add a new soft clause with the weight of the core.
      addSoftClause(weightCore, clause, vars);

      Lit l = newLiteral();
      // Create a new assumption literal.
      softClauses[nSoft() - 1].assumptionVar = l;
      coreMapping[l] =
          nSoft() - 1;  // Map the new soft clause to its assumption literal.
      assumps.push(~l); // Update the assumption vector.

      if (symmetryStrategy) symmetryLog(nSoft() - 1);
    }
  }
  encodeEO(lits);
  sumSizeCores += conflict.size();
}

/*_________________________________________________________________________________________________
  |
  |  computeCostCore : (conflict : vec<Lit>&)  ->  [int]
  |
  |    Description:
  |
  |      Computes the cost of the core. The cost of a core is the minimum weight
  |      of the soft clauses that appear in that core.
  |
  |    Pre-conditions:
  |      * Assumes that 'conflict' is not empty.
  |
  |________________________________________________________________________________________________@*/
int WBO::computeCostCore(vec<Lit> &conflict)
{

  assert(conflict.size() != 0);

  if (problemType == _UNWEIGHTED_)
  {
    return 1;
  }

  int coreCost = INT32_MAX;

  for (int i = 0; i < conflict.size(); i++)
  {
    int indexSoft = coreMapping[conflict[i]];
    if (softClauses[indexSoft].weight < coreCost)
      coreCost = softClauses[indexSoft].weight;
  }

  return coreCost;
}

/************************************************************************************************
 //
 // Symmetry breaking methods
 //
 ************************************************************************************************/

// Initializes the mapping from soft clauses with the index of the cores where
// they appear
void WBO::initSymmetry()
{

  for (int i = 0; i < nSoft(); i++)
  {
    softMapping.push();
    relaxationMapping.push();
    new (&softMapping[i]) vec<Lit>();
    new (&relaxationMapping[i]) vec<Lit>();
  }
}

/*_________________________________________________________________________________________________
  |
  |  symmetryLog : (p : int) ->  [void]
  |
  |  Description:
  |
  |    Adds the current core index ('nbCores')  to the vector of cores of the
  |    soft clause with index 'p'.
  |
  |  Pre-conditions:
  |    * Assumes that the soft clause with index 'p' has been relaxed.
  |
  |  Post-conditions:
  |    * 'softMapping' of the soft clause with index 'p' is updated with the
  |      core index 'nbCores'.
  |    * Soft clause with index 'p' is added to 'indexSoftCore'.
  |
  |________________________________________________________________________________________________@*/
void WBO::symmetryLog(int p)
{

  if (nbSymmetryClauses < symmetryBreakingLimit)
  {

    // If the soft clause was duplicated then it may happen 'p' is larger than
    // 'softMapping.size()'.
    // In this case, we increase the vector softMapping until the index 'p'.
    while (softMapping.size() <= p)
    {
      softMapping.push();
      relaxationMapping.push();
      new (&softMapping[softMapping.size() - 1]) vec<Lit>();
      new (&relaxationMapping[relaxationMapping.size() - 1]) vec<Lit>();
    }

    softMapping[p].push(nbCores);
    // If a soft clause is duplicated, then only relaxation variables after the
    // duplication are considered.
    // Note: This is the difference between relaxationMapping[p] and
    // softClauses[p].relaxationVars.
    relaxationMapping[p].push(softClauses[p].relaxationVars.last());
    // If 'softMapping[p].size()' is equal to 1 then the soft clause only appear
    // in one core.
    // Symmetry breaking only applies when the soft clause has appeared in
    // previous cores.
    if (softMapping[p].size() > 1) indexSoftCore.push(p);
  }
}

/*_________________________________________________________________________________________________
  |
  |  symmetryBreaking : [void] ->  [void]
  |
  |  Description:
  |
  |    Adds binary clauses to the hard clauses to break symmetries between
  |    relaxation variables of soft clauses that have been relaxed multiple
  |    times.
  |    NOTE: This method may produce a large number of binary clauses.
  |    'symmetryBreakingLimit' can be used to control the maximum number of
  |    clauses added by this method.
  |
  |  For further details see:
  |    * Carlos Ansótegui, Maria Luisa Bonet, Joel Gabàs, Jordi Levy: Improving
  |      SAT-Based Weighted MaxSAT Solvers. CP 2012: 86-101
  |
  |  Post-conditions:
  |    * 'duplicatedSymmetry' is updated.
  |    * 'hardClauses' are updated with the binary clauses that break symmetries
  |       between relaxation variables.
  |    * 'nbSymmetryClauses' is updated.
  |
  |________________________________________________________________________________________________@*/
void WBO::symmetryBreaking()
{

  if (indexSoftCore.size() != 0 && nbSymmetryClauses < symmetryBreakingLimit)
  {
    vec<Lit> *coreIntersection =
        new vec<Lit>[nbCores]; // Relaxation variables of soft clauses that
                               // appear in the current core stored by core
                               // index
    vec<Lit> *coreIntersectionCurrent =
        new vec<Lit>[nbCores]; // Relaxation variables of soft clauses that
                               // appear in previous cores that intersect with
                               // the current core stored by core index
    vec<int> coreList; // Indexes of cores that have soft clauses in common with
                       // the current core

    for (int i = 0; i < indexSoftCore.size(); i++)
    {
      int p = indexSoftCore[i];

      vec<int> addCores; // Cores where the soft clause with index 'p' appeared
      for (int j = 0; j < softMapping[p].size() - 1; j++)
      {
        int core = softMapping[p][j];
        addCores.push(core);
        if (coreIntersection[core].size() == 0) coreList.push(core);
        assert(j < relaxationMapping[p].size());
        assert(var(relaxationMapping[p][j]) > nbInitialVariables);
        coreIntersection[core].push(relaxationMapping[p][j]);
      }

      for (int j = 0; j < addCores.size(); j++)
      {
        int core = addCores[j];
        int b = softMapping[p].size() - 1;
        assert(b < relaxationMapping[p].size());
        assert(var(relaxationMapping[p][b]) > nbInitialVariables);
        coreIntersectionCurrent[core].push(relaxationMapping[p][b]);
      }

      for (int k = 0; k < coreList.size(); k++)
      {
        for (int i = 0; i < coreIntersection[coreList[k]].size(); i++)
        {
          for (int j = i + 1; j < coreIntersectionCurrent[coreList[k]].size();
               j++)
          {
            vec<Lit> clause;
            clause.push(~coreIntersection[coreList[k]][i]);
            clause.push(~coreIntersectionCurrent[coreList[k]][j]);

            // Symmetry clauses are binary clauses. This method may introduce
            // duplicated clauses.
            // The set 'duplicatedSymmetryClauses' is used to prevent adding
            // duplicated clauses.
            symmetryClause symClause;
            symClause.first = var(coreIntersection[coreList[k]][i]);
            symClause.second = var(coreIntersectionCurrent[coreList[k]][j]);
            if (var(coreIntersection[coreList[k]][i]) >
                var(coreIntersectionCurrent[coreList[k]][j]))
            {
              symClause.first = var(coreIntersectionCurrent[coreList[k]][j]);
              symClause.second = var(coreIntersection[coreList[k]][i]);
            }

            if (duplicatedSymmetryClauses.find(symClause) ==
                duplicatedSymmetryClauses.end())
            {
              duplicatedSymmetryClauses.insert(symClause);
              addHardClause(clause);
              nbSymmetryClauses++;
              // If the number of symmetry clauses reached the limit then we
              // stop adding them.
              // NOTE:	This limit has not been proposed in the original paper.
              //				It may be used here to prevent
              // possible memory problems.
              if (symmetryBreakingLimit == nbSymmetryClauses) break;
            }
          }
          if (symmetryBreakingLimit == nbSymmetryClauses) break;
        }
        if (symmetryBreakingLimit == nbSymmetryClauses) break;
      }
      if (symmetryBreakingLimit == nbSymmetryClauses) break;
    }
    delete[] coreIntersection;
    delete[] coreIntersectionCurrent;
  }

  indexSoftCore.clear();
}

/************************************************************************************************
 //
 // WBO search
 //
 ************************************************************************************************/

/*_________________________________________________________________________________________________
  |
  |  unsatSearch : [void] ->  [void]
  |
  |  Description:
  |
  |    Calls a SAT solver only on the hard clauses of the MaxSAT formula.
  |    If the hard clauses are unsatisfiable then the MaxSAT solver terminates
  |    and returns 'UNSATISFIABLE'.
  |    Otherwise, a model has been found and it is stored. Without this call,
  |    the termination of the MaxSAT solver is not guaranteed.
  |
  |  For further details see:
  |    * Carlos Ansótegui, Maria Luisa Bonet, Jordi Levy: SAT-based MaxSAT
  |      algorithms. Artif. Intell. 196: 77-105 (2013)
  |
  |  Post-conditions:
  |   * If the hard clauses are satisfiable then 'ubCost' is updated to the cost
  |     of the model.
  |   * If the working formula is satisfiable, then 'nbSatisfiable' is increased
  |     by 1. Otherwise, 'nbCores' is increased by 1.
  |
  |________________________________________________________________________________________________@*/
void WBO::unsatSearch()
{

  assert(assumptions.size() == 0);

  solver = rebuildHardSolver();
  lbool res = searchSATSolver(solver, assumptions);

  if (res == l_False)
  {
    nbCores++;
    printAnswerAndExit(_UNSATISFIABLE_);
    exit(_UNSATISFIABLE_);
  }
  else if (res == l_True)
  {
    nbSatisfiable++;
    uint64_t cost = computeCostModel(solver->model);
    assert(cost <= ubCost);
    ubCost = cost;
    saveModel(solver->model);
    if ((verbosity > 0) && (nSoft() > 0)) printf("o %" PRIu64 "\n", ubCost);
  }

  delete solver;
  solver = NULL;
}

/*_________________________________________________________________________________________________
  |
  |  weightSearch : [void] ->  [void]
  |
  |  Description:
  |
  |    MaxSAT weight-based search. Considers the weights of soft clauses to find
  |    cores with larger weights first.
  |
  |  For further details see:
  |    * Ruben Martins, Vasco Manquinho, Ines Lynce: On Partitioning for Maximum
  |      Satisfiability. ECAI 2012: 913-914
  |    * Carlos Ansótegui, Maria Luisa Bonet, Joel Gabàs, Jordi Levy: Improving
  |      SAT-Based Weighted MaxSAT Solvers. CP 2012: 86-101
  |
  |  Pre-conditions:
  |    * Assumes 'weightStrategy' to be '_WEIGHT_NORMAL_' or
  |      '_WEIGHT_DIVERSIFY_'.
  |
  |  Post-conditions:
  |    * 'lbCost' is updated.
  |    * 'ubCost' is updated.
  |    * 'nbSatisfiable' is updated.
  |    * 'nbCores' is updated.
  |________________________________________________________________________________________________@*/
void WBO::weightSearch()
{

  assert(weightStrategy == _WEIGHT_NORMAL_ ||
         weightStrategy == _WEIGHT_DIVERSIFY_);

  unsatSearch();

  initAssumptions(assumptions);
  updateCurrentWeight(weightStrategy);
  solver = rebuildWeightSolver(weightStrategy);

  for (;;)
  {

    lbool res = searchSATSolver(solver, assumptions);

    if (res == l_False)
    {
      nbCores++;
      assert(solver->conflict.size() > 0);
      int coreCost = computeCostCore(solver->conflict);
      lbCost += coreCost;
      if (verbosity > 0)
        printf("c LB : %-12" PRIu64 " CS : %-12d W  : %-12d\n", lbCost,
               solver->conflict.size(), coreCost);
      relaxCore(solver->conflict, coreCost, assumptions);
      delete solver;
      solver = rebuildWeightSolver(weightStrategy);
    }

    if (res == l_True)
    {
      nbSatisfiable++;
      if (nbCurrentSoft == nSoft())
      {
        assert(computeCostModel(solver->model) == lbCost);
        if (lbCost == ubCost && verbosity > 0) printf("c LB = UB\n");
        if (lbCost < ubCost)
        {
          ubCost = lbCost;
          saveModel(solver->model);
          if ((verbosity > 0) && (nSoft() > 0)) printf("o %" PRIu64 "\n", lbCost);
        }
        printAnswerAndExit(_OPTIMUM_);
        exit(_OPTIMUM_);
      }
      else
      {
        updateCurrentWeight(weightStrategy);
        uint64_t cost = computeCostModel(solver->model);
        if (cost < ubCost)
        {
          ubCost = cost;
          saveModel(solver->model);
          if ((verbosity > 0) && (nSoft() > 0)) printf("o %" PRIu64 "\n", ubCost);
        }

        if (lbCost == ubCost)
        {
          if (verbosity > 0) printf("c LB = UB\n");
          printAnswerAndExit(_OPTIMUM_);
          exit(_OPTIMUM_);
        }

        delete solver;
        solver = rebuildWeightSolver(weightStrategy);
      }
    }
  }
}

/*_________________________________________________________________________________________________
  |
  |  normalSearch : [void] ->  [void]
  |
  |  Description:
  |
  |    Original WBO algorithm.
  |
  |  For further details see:
  |    * Vasco Manquinho, Joao Marques-Silva, Jordi Planes: Algorithms for
  |      Weighted Boolean Optimization. SAT 2009: 495-508
  |
  |  Post-conditions:
  |    * 'lbCost' is updated.
  |    * 'ubCost' is updated.
  |    * 'nbSatisfiable' is updated.
  |    * 'nbCores' is updated.
  |
  |________________________________________________________________________________________________@*/
void WBO::normalSearch()
{

  unsatSearch();

  initAssumptions(assumptions);
  solver = rebuildSolver();

  for (;;)
  {

    lbool res = searchSATSolver(solver, assumptions);

    if (res == l_False)
    {
      nbCores++;
      assert(solver->conflict.size() > 0);
      int coreCost = computeCostCore(solver->conflict);
      lbCost += coreCost;
      if (verbosity > 0)
        printf("c LB : %-12" PRIu64 " CS : %-12d W  : %-12d\n", lbCost,
               solver->conflict.size(), coreCost);

      if (lbCost == ubCost)
      {
        if (verbosity > 0) printf("c LB = UB\n");
        printAnswerAndExit(_OPTIMUM_);
        exit(_OPTIMUM_);
      }

      relaxCore(solver->conflict, coreCost, assumptions);
      delete solver;
      solver = rebuildSolver();
    }

    if (res == l_True)
    {
      nbSatisfiable++;
      ubCost = computeCostModel(solver->model);
      assert(lbCost == ubCost);
      if ((verbosity > 0) && (nSoft() > 0)) printf("o %" PRIu64 "\n", lbCost);
      saveModel(solver->model);
      printAnswerAndExit(_OPTIMUM_);
      exit(_OPTIMUM_);
    }
  }
}

// Public search method
void WBO::search()
{
  printConfiguration();

  nbInitialVariables = nVars();

  // If the maximum weight of the soft clauses is 1 then the problem is
  // considered unweighted.
  if (currentWeight == 1)
  {
    problemType = _UNWEIGHTED_;
    weightStrategy = _WEIGHT_NONE_;
  }

  if (symmetryStrategy) initSymmetry();

  if (problemType == _UNWEIGHTED_ || weightStrategy == _WEIGHT_NONE_)
    normalSearch();
  else if (weightStrategy == _WEIGHT_NORMAL_ ||
           weightStrategy == _WEIGHT_DIVERSIFY_)
    weightSearch();
}

/************************************************************************************************
 //
 // Other protected methods
 //
 ************************************************************************************************/

/*_________________________________________________________________________________________________
  |
  |  initAssumptions : (assumps : vec<Lit>&) ->  [void]
  |
  |  Description:
  |
  |    Creates a new assumption literal for each soft clause and initializes the
  |    assumption vector with negation of this literal. Assumptions are used to
  |    extract cores.
  |
  |  Post-conditions:
  |    * For each soft clause 'i' creates an assumption literal and assigns it
  |      to 'softClauses[i].assumptionVar'.
  |    * 'coreMapping' is updated by mapping each assumption literal with the
  |      corresponding index of each soft clause.
  |    * 'assumps' is updates with the assumptions literals.
  |
  |________________________________________________________________________________________________@*/
void WBO::initAssumptions(vec<Lit> &assumps)
{
  for (int i = 0; i < nbSoft; i++)
  {
    Lit l = newLiteral();
    softClauses[i].assumptionVar = l;
    coreMapping[l] = i;
    assumps.push(~l);
  }
}

// Print WBO configuration.
void WBO::print_WBO_configuration(int ws, bool sb, int slim)
{
	if (verbosity > 0)
	{
		printf("c |  Algorithm: %23s                                             "
		       "                      |\n",
		       "WBO");
		char ws_char[10];
		if (ws == 0)
			strcpy(ws_char, "None");
		else if (ws == 1)
			strcpy(ws_char, "Weight");
		else if (ws == 2)
			strcpy(ws_char, "Diversity");
		if (problemType == _WEIGHTED_)
			printf("c |  Weight-Strategy: %17s                                         "
			       "    "
			       "                      |\n",
			       ws_char);
		if (sb)
			printf("c |  Symmetry-Breaking: %15s                                       "
			       "      "
			       "                      |\n",
			       "On");
		else
			printf("c |  Symmetry-Breaking: %15s                                       "
			       "      "
			       "                      |\n",
			       "Off");
		printf(
		       "c |  Symmetry-Limit: %18d                                             "
		       "                      |\n",
		       slim);
	}
}
