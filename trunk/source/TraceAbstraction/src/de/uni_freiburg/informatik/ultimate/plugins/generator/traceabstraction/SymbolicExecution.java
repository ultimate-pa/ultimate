package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.SortedMap;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.ExternalSolver;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.DefaultTransFormulas;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.NestedFormulas;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.NestedSsaBuilder;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;

public class SymbolicExecution<LETTER extends IAction, STATE> {

	private final INestedWordAutomaton<LETTER, STATE> mAbstraction;
	private final ManagedScript mMgdScript;
	protected final SymbolicExecutionLock mSymExecCheckLock = new SymbolicExecutionLock();
	protected final STATE mDummyEmptyStackState;

	NestedRun<LETTER, STATE> mCounterexample;

	// this stuff is needed only for asserting / ssa
	private final CfgSmtToolkit mCsToolkit;
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	// private final boolean mOverapproximatedWithLoopBound = false;
	private final boolean mSolverReturnedUnknown = false;
	private final boolean mSafe;

	// TC Solver setup
	TaCheckAndRefinementPreferences<?> mPrefs;
	TaskIdentifier mTaskIdentifier = null;
	private final SymExecWorkerThread mSymExecWorkerThread;
	private final ManagedScript mMainMgdScript;
	private final TAPreferences mPref;

	/**
	 *
	 * @param csToolkit
	 * @param logger
	 * @param services
	 * @param preferences
	 * @throws InterruptedException
	 * @throws AutomataLibraryException
	 *
	 */
	public SymbolicExecution(final IUltimateServiceProvider services, final ILogger logger,
			final TaCheckAndRefinementPreferences prefs, final CfgSmtToolkit csToolkit,
			final ManagedScript mainMgdScript, final INestedWordAutomaton<LETTER, STATE> abstraction,
			final TaskIdentifier taskIdentifier, final SymExecWorkerThread symExecWorkerThread,
			final TAPreferences preferences) throws AutomataLibraryException, InterruptedException {
		mAbstraction = abstraction;
		mMainMgdScript = mainMgdScript;
		mDummyEmptyStackState = mAbstraction.getEmptyStackState();
		mCsToolkit = csToolkit;
		mLogger = logger;
		mServices = services;
		mTaskIdentifier = taskIdentifier;
		mPrefs = prefs;
		mSymExecWorkerThread = symExecWorkerThread;
		mMgdScript = csToolkit.createFreshManagedScript(mServices, getSolverSetting(), "SymExec");
		mPref = preferences;
		mSafe = run();
	}

	/**
	 * Runs Symbolic Execution on the abstraction, returns true if the program is guaranteed to be save.
	 *
	 * @return
	 */
	private boolean run() {
		mMgdScript.lock(mSymExecCheckLock);
		mMgdScript.push(mSymExecCheckLock, 1);
		// TODO Auto-generated method stub

		// TODO symbolic execution
		mMgdScript.pop(mSymExecCheckLock, 1);
		mMgdScript.unlock(mSymExecCheckLock);
		mLogger.info("is safe " + (mSafe && !mSolverReturnedUnknown));
		mLogger.info("solver returned unknown: " + mSolverReturnedUnknown);
		return false;
	}

	private SolverSettings getSolverSetting() {
		final SolverSettings setting;
		switch (mPrefs.getRefinementStrategy()) {
		case RefinementStrategy.CAMEL: {
			setting = mPrefs.constructSolverSettings(new SubtaskIterationIdentifier(mTaskIdentifier, 1))
					.setUseExternalSolver(ExternalSolver.Z3).setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode);
			break;
		}
		case RefinementStrategy.FOX: {
			setting = mPrefs.constructSolverSettings(new SubtaskIterationIdentifier(mTaskIdentifier, 1))
					.setUseExternalSolver(ExternalSolver.MATHSAT)
					.setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode);
			break;
		}
		default: {
			setting = mPrefs.constructSolverSettings(new SubtaskIterationIdentifier(mTaskIdentifier, 1))
					.setUseExternalSolver(ExternalSolver.CVC5)
					.setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode);
			break;
		}
		}
		return setting;
	}

	public boolean isSafe() {
		return mSafe;
	}

	public boolean wasOverapproximated() {
		return mSolverReturnedUnknown;
	}

	public boolean wasUnkown() {
		return mSolverReturnedUnknown;
	}

	public NestedRun<LETTER, STATE> getCounterexample() {
		assert !mSafe;
		return mCounterexample;
	}

	private NestedFormulas<LETTER, UnmodifiableTransFormula, IPredicate>
			createNestedFormulas(final NestedRun<LETTER, STATE> trace) {
		final NestedWord<LETTER> nw = trace.getWord();
		final BasicPredicateFactory bpf = new BasicPredicateFactory(mServices, mMgdScript, mCsToolkit.getSymbolTable());
		final BasicPredicate truePred = bpf.newPredicate(mMgdScript.getScript().term("true"));
		final BasicPredicate falsePred = bpf.newPredicate(mMgdScript.getScript().term("false"));
		final SortedMap<Integer, IPredicate> pendingContexts = new TreeMap<>();
		final NestedFormulas<LETTER, UnmodifiableTransFormula, IPredicate> rv = new DefaultTransFormulas<>(nw, truePred,
				falsePred, pendingContexts, mCsToolkit.getOldVarsAssignmentCache(), false);
		return rv;
	}

	/**
	 * Creates the SSA, asserts the formula to the solver. The solver stack has to be empty.
	 *
	 * @param trace
	 */
	private void isTraceFeasible(final NestedRun<LETTER, STATE> trace) {
		mMgdScript.pop(mSymExecCheckLock, 1);
		mMgdScript.push(mSymExecCheckLock, 1);
		final NestedFormulas<LETTER, UnmodifiableTransFormula, IPredicate> nestedFormulas = createNestedFormulas(trace);
		final NestedSsaBuilder<LETTER> mNsb = new NestedSsaBuilder<>(mMgdScript, mCsToolkit, nestedFormulas, mLogger);
		final NestedFormulas<LETTER, Term, Term> ssa = mNsb.getSsa();
		final TermTransferrer mainToWorker = new TermTransferrer(mMainMgdScript.getScript(), mMgdScript.getScript());

		for (int i = 0; i < trace.getWord().length(); i++) {
			if (trace.isCallPosition(i)) {
				mMgdScript.assertTerm(mSymExecCheckLock, mainToWorker.transform(ssa.getGlobalVarAssignment(i)));
				mMgdScript.assertTerm(mSymExecCheckLock, mainToWorker.transform(ssa.getLocalVarAssignment(i)));
				mMgdScript.assertTerm(mSymExecCheckLock, mainToWorker.transform(ssa.getOldVarAssignment(i)));
			} else {
				mMgdScript.assertTerm(mSymExecCheckLock, mainToWorker.transform(ssa.getFormulaFromNonCallPos(i)));
			}
		}
	}

	/**
	 * Package private class used by Symbolic Execution to lock the {@link ManagedScript}.
	 */
	static class SymbolicExecutionLock {
	}
}
