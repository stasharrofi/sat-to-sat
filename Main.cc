/*****************************************************************************************[Main.cc]
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

#include <errno.h>

#include <signal.h>
#include <zlib.h>

#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "core/SolverTypes.h"
#include "Dimacs.h"
#include "STSParser.h"
#include "core/Solver.h"

using namespace Minisat;

//=================================================================================================


void printStats(Solver& solver)
{
    double cpu_time = cpuTime();
    double mem_used = memUsedPeak();
    printf("c restarts              : %" PRIu64"\n", solver.starts);
    printf("c conflicts             : %-12" PRIu64"   (%.0f /sec)\n", solver.conflicts   , solver.conflicts   /cpu_time);
    printf("c decisions             : %-12" PRIu64"   (%4.2f %% random) (%.0f /sec)\n", solver.decisions, (float)solver.rnd_decisions*100 / (float)solver.decisions, solver.decisions   /cpu_time);
    printf("c propagations          : %-12" PRIu64"   (%.0f /sec)\n", solver.propagations, solver.propagations/cpu_time);
    printf("c conflict literals     : %-12" PRIu64"   (%4.2f %% deleted)\n", solver.tot_literals, (solver.max_literals - solver.tot_literals)*100 / (double)solver.max_literals);
    if (mem_used != 0) printf("c Memory used           : %.2f MB\n", mem_used);
    printf("c CPU time              : %g s\n", cpu_time);
}


static IntOption opt_model_count("Model", "n", "The number of models printed (0=all models)", 1, IntRange(0, 100));
static IntOption opt_input_format("Interface", "in-format", "Input format (0=DIMACD, 1=STS)", 0, IntRange(0, 1));

static MaxSAT* mxsolver;

// Note that '_exit()' rather than 'exit()' has to be used. The reason is that 'exit()' calls
// destructors and may cause deadlocks if a malloc/free function happens to be running (these
// functions are guarded by locks for multithreaded use).
static void SIGINT_exit(int signum)
{
  mxsolver->printAnswerAndExit(_UNKNOWN_);
  _exit(_UNKNOWN_);
}

//=================================================================================================
// Main:


int main(int argc, char** argv)
{
	try
	{
		setUsageHelp("USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n");

		// Extra options:
		//
		IntOption    verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 1, IntRange(0, 2));
		IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", INT32_MAX, IntRange(0, INT32_MAX));
		IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", INT32_MAX, IntRange(0, INT32_MAX));
		BoolOption   drup   ("MAIN", "drup",   "Generate DRUP UNSAT proof.", false);
		StringOption drup_file("MAIN", "drup-file", "DRUP UNSAT proof ouput file.", "");

		parseOptions(argc, argv, true);

		if (verb > 0)
			printf("c This is graphsat.\n");

#if defined(__linux__)
		fpu_control_t oldcw, newcw;
		_FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
		if (verb > 0)
			printf("c WARNING: for repeatability, setting FPU to use double precision\n");
#endif

		double initial_time = cpuTime();
		mxsolver = MaxSAT::create(initial_time, verb);

		// Use signal handlers that forcibly quit until the solver will be able to respond to
		// interrupts:
		signal(SIGXCPU, SIGINT_exit);
		signal(SIGTERM, SIGINT_exit);
		signal(SIGINT, SIGINT_exit);

		// Set limit on CPU-time:
		if (cpu_lim != INT32_MAX)
		{
			rlimit rl;
			getrlimit(RLIMIT_CPU, &rl);
			if (rl.rlim_max == RLIM_INFINITY || (rlim_t)cpu_lim < rl.rlim_max)
			{
				rl.rlim_cur = cpu_lim;
				if (setrlimit(RLIMIT_CPU, &rl) == -1)
					printf("c WARNING! Could not set resource limit: CPU-time.\n");
			}
		}

		// Set limit on virtual memory:
		if (mem_lim != INT32_MAX)
		{
			rlim_t new_mem_lim = (rlim_t)mem_lim * 1024*1024;
			rlimit rl;
			getrlimit(RLIMIT_AS, &rl);
			if (rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max)
			{
				rl.rlim_cur = new_mem_lim;
				if (setrlimit(RLIMIT_AS, &rl) == -1)
					printf("c WARNING! Could not set resource limit: Virtual memory.\n");
			}
		}

		if ((argc == 1) && (verb > 0))
			printf("c Reading from standard input... Use '--help' for help.\n");

		gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
		if (in == NULL)
			printf("c ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);

		if (mxsolver->getVerbosity() > 0)
		{
			printf("c ============================[ Problem Statistics ]=============================\n");
			printf("c |                                                                             |\n");
		}

		if (opt_input_format == 0)
			parse_DIMACS(in, *mxsolver);
		else
			parse_STS(in, *mxsolver);
		gzclose(in);
		FILE* res = (argc >= 3) ? fopen(argv[2], "wb") : stdout;

		if (mxsolver->getVerbosity() > 0)
		{
			printf("c |  Number of variables:    %12d                                       |\n", mxsolver->nVars());
			if (mxsolver->hasMinimization())
			{
				printf("c |  Number of hard clauses: %12d                                       |\n", mxsolver->nHard());
				printf("c |  Number of soft clauses: %12d                                       |\n", mxsolver->nSoft());
			}
			else
				printf("c |  Number of clauses:      %12d                                       |\n", mxsolver->nHard());
		}

		double parsed_time = cpuTime();
		if (mxsolver->getVerbosity() > 0)
		{
			printf("c |  Parse time:           %12.2f s                                       |\n", parsed_time - initial_time);
			printf("c |                                                                             |\n");
		}

		int ret_value;
		if (mxsolver->hasMinimization())
		{
			mxsolver = MaxSAT::recreate(mxsolver);
			mxsolver->search();
			ret_value = _OPTIMUM_;
		}
		else
		{
			Solver *S = mxsolver->getPrototypeSolver();
			S->verbosity = mxsolver->getVerbosity();

			if (!S->simplify())
			{
				if (mxsolver->getVerbosity() > 0)
					fprintf(res, "c Solved by unit propagation!");
				fprintf(res, "s UNSAT\n");
				ret_value = _UNSATISFIABLE_;
			}
			else
			{
				lbool ret;
				vec<Lit> dummy;
				int currentModelCount = 0;
				int expectedModelCount = opt_model_count;
				while (true)
				{
					ret = S->solveLimited(dummy);
					if (mxsolver->getVerbosity() > 0)
					{
						printStats(*S);
						printf("\n");
					}

					if (ret == l_True)
					{
						currentModelCount++;
						fprintf(res, "s SAT\n");
						S->printModel(res);
						if (currentModelCount == expectedModelCount)
							break;
						else
						{
							vec<Lit> modelBlocker;
							for (int i = 0; i < S->decisionLits.size(); i++)
								modelBlocker.push(~(S->decisionLits[i]));
							S->addClause(modelBlocker);
						}
					}
					else if (ret == l_False)
					{
						fprintf(res, "s UNSAT\n");
						if (currentModelCount > 0)
							ret = l_True;
						break;
					}
					else
					{
						fprintf(res, "s INDET\n");
						break;
					}
				}
				ret_value = (ret == l_True ? _SATISFIABLE_ : ret == l_False ? _UNSATISFIABLE_ : _UNKNOWN_);
			}
		}
		if (res != stdout)
			fclose(res);

		return ret_value;
	}
	catch (OutOfMemoryException&)
	{
		printf("c ===============================================================================\n");
		printf("s INDETERMINATE\n");
		exit(0);
	}
}