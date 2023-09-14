/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.IRunningTaskStackProvider;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IActionWithBranchEncoders;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrderType;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.ExceptionHandlingCategory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.Reason;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.TraceCheckerUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Check if a trace fulfills a specification. Provides an execution (that violates the specification) if the check was
 * negative.
 * <p>
 * Given
 * <ul>
 * <li>a precondition stated by predicate φ_0
 * <li>a postcondition stated by predicate φ_n
 * <li>a trace (which is a word of CodeBlocks) cb_0 cb_2 ... cb_{n-1},
 * </ul>
 * check if the trace always fulfills the postcondition φ_n if the precondition φ_0 holds before the execution of the
 * trace, i.e. we check if the following inclusion of predicates is valid. post(φ_0, cb_1 cb_2 ... cb_n) ⊆ φ_n
 * <p>
 * A feasibility check of a trace can be seen as the special case of this trace check. A trace is feasible if and only
 * if the trace does not fulfill the specification given by the precondition <i>true</i> and the postcondition
 * <i>false</i>. See Example1.
 * <p>
 * Example1: If
 * <ul>
 * <li>the precondition is the predicate <i>true</i>,
 * <li>the postcondition is the predicate <i>false</i>,
 * <li>and the trace cb_0 cb_1 is x:=0; x!=-1;,
 * </ul>
 * <p>
 * then the trace fulfills its specification.
 * <p>
 * Example2: If
 * <ul>
 * <li>the precondition is the predicate x==0,
 * <li>the postcondition is the predicate x==1,
 * <li>and the trace cb_0 cb_1 is x++; x++;,
 * </ul>
 * <p>
 * then the trace does not fulfill its specification.
 * <p>
 *
 * @author heizmann@informatik.uni-freiburg.de
 */
public class TraceCheck<L extends IAction> implements ITraceCheck<L> {

	protected final ILogger mLogger;
	protected final IUltimateServiceProvider mServices;
	/**
	 * After constructing a new traceCheck satisfiability of the trace was checked. However, the trace check is not yet
	 * finished, and the SmtManager is still locked by this traceCheck to allow the computation of an interpolants or an
	 * execution. The trace check is only finished after the unlockSmtManager() method was called.
	 */
	protected boolean mTraceCheckFinished;
	protected final CfgSmtToolkit mCsToolkit;
	/**
	 * Interface for query the SMT solver.
	 */
	protected final ManagedScript mCfgManagedScript;
	protected final ManagedScript mTcSmtManager;
	protected final TraceCheckLock mTraceCheckLock = new TraceCheckLock();
	/**
	 * Maps a procedure name to the set of global variables which may be modified by the procedure. The set of variables
	 * is represented as a map where the identifier of the variable is mapped to the type of the variable.
	 */
	protected final NestedWord<L> mTrace;
	protected final IPredicate mPrecondition;
	protected final IPredicate mPostcondition;
	/**
	 * If the trace contains "pending returns" (returns without corresponding calls) we have to provide a predicate for
	 * each pending return that specifies what held in the calling context to which we return. (If the trace would
	 * contain the corresponding call, this predicate would be the predecessor of the call). We call these predicates
	 * "pending contexts". These pending contexts are provided via a mapping from the position of the pending return
	 * (given as Integer) to the predicate.
	 */
	protected final SortedMap<Integer, IPredicate> mPendingContexts;
	protected AnnotateAndAsserter<L> mAAA;
	protected final boolean mProvidesIcfgProgramExecution;
	protected final IcfgProgramExecution<L> mRcfgProgramExecution;
	protected final NestedFormulas<L, UnmodifiableTransFormula, IPredicate> mNestedFormulas;
	protected NestedSsaBuilder<L> mNsb;
	protected final TraceCheckStatisticsGenerator mTraceCheckBenchmarkGenerator;
	protected final AssertCodeBlockOrder mAssertCodeBlockOrder;
	protected final IIcfgSymbolTable mBoogie2SmtSymbolTable;
	protected final FeasibilityCheckResult mFeasibilityResult;

	/**
	 * Check if trace fulfills specification given by precondition, postcondition and pending contexts. The
	 * pendingContext maps the positions of pending returns to predicates which define possible variable valuations in
	 * the context to which the return leads the trace.
	 */
	public TraceCheck(final IPredicate precondition, final IPredicate postcondition,
			final SortedMap<Integer, IPredicate> pendingContexts, final NestedWord<L> trace,
			final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final AssertCodeBlockOrder assertCodeBlockOrder, final boolean computeRcfgProgramExecution,
			final boolean collectInterpolatSequenceStatistics) {
		this(precondition, postcondition, pendingContexts, trace,
				new DefaultTransFormulas<>(trace, precondition, postcondition, pendingContexts,
						csToolkit.getOldVarsAssignmentCache(), false),
				services, csToolkit, assertCodeBlockOrder, computeRcfgProgramExecution,
				collectInterpolatSequenceStatistics, true);
	}

	protected TraceCheck(final IPredicate precondition, final IPredicate postcondition,
			final SortedMap<Integer, IPredicate> pendingContexts, final NestedWord<L> trace,
			final NestedFormulas<L, UnmodifiableTransFormula, IPredicate> rv, final IUltimateServiceProvider services,
			final CfgSmtToolkit csToolkit, final AssertCodeBlockOrder assertCodeBlockOrder,
			final boolean computeRcfgProgramExecution, final boolean collectInterpolatSequenceStatistics,
			final boolean unlockSmtSolverAlsoIfUnsat) {
		this(precondition, postcondition, pendingContexts, trace, rv, services, csToolkit, csToolkit.getManagedScript(),
				assertCodeBlockOrder, computeRcfgProgramExecution, collectInterpolatSequenceStatistics,
				unlockSmtSolverAlsoIfUnsat);
	}

	/**
	 * Commit additionally the DefaultTransFormulas
	 *
	 * @param services
	 */
	protected TraceCheck(final IPredicate precondition, final IPredicate postcondition,
			final SortedMap<Integer, IPredicate> pendingContexts, final NestedWord<L> trace,
			final NestedFormulas<L, UnmodifiableTransFormula, IPredicate> rv, final IUltimateServiceProvider services,
			final CfgSmtToolkit csToolkit, final ManagedScript managedScriptTc,
			final AssertCodeBlockOrder assertCodeBlockOrder, final boolean computeRcfgProgramExecution,
			final boolean collectInterpolatSequenceStatistics, final boolean unlockSmtSolverAlsoIfUnsat) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(TraceCheckerUtils.PLUGIN_ID);
		mCfgManagedScript = csToolkit.getManagedScript();
		mTcSmtManager = managedScriptTc;
		mCsToolkit = csToolkit;
		mBoogie2SmtSymbolTable = csToolkit.getSymbolTable();
		if (trace.length() == 0) {
			throw new IllegalArgumentException(
					"Only non-empty traces supported. For empty traces we are unable to determine the procedure in which precondition and postcondition are evaluated (needed to check whether a global var and the corresponding oldvar are equivalent)");
		}
		mTrace = trace;
		mPrecondition = precondition;
		mPostcondition = postcondition;
		if (pendingContexts == null) {
			throw new IllegalArgumentException(
					"pendingContexts must not be null; if there are no pending contexts, use an empty map");
		}
		mPendingContexts = pendingContexts;
		mNestedFormulas = rv;
		mAssertCodeBlockOrder = assertCodeBlockOrder;
		mTraceCheckBenchmarkGenerator = new TraceCheckStatisticsGenerator(collectInterpolatSequenceStatistics);

		boolean providesIcfgProgramExecution = false;
		IcfgProgramExecution<L> icfgProgramExecution = null;
		FeasibilityCheckResult feasibilityResult = null;
		try {
			feasibilityResult = checkTrace();
			if (feasibilityResult.getLBool() == LBool.UNKNOWN
					&& feasibilityResult.getReasonUnknown().getReason() == Reason.ULTIMATE_TIMEOUT) {
				throw new ToolchainCanceledException(getClass(), "checking feasibility of error trace");
			}
			if (feasibilityResult.getLBool() == LBool.UNSAT) {
				if (unlockSmtSolverAlsoIfUnsat) {
					mTraceCheckFinished = true;
					cleanupAndUnlockSolver();
				}
			} else if (computeRcfgProgramExecution && feasibilityResult.getLBool() == LBool.SAT) {
				icfgProgramExecution = computeRcfgProgramExecutionAndDecodeBranches(managedScriptTc);
				if (icfgProgramExecution != null) {
					providesIcfgProgramExecution = true;
				}
				mTraceCheckFinished = true;
			} else if (!feasibilityResult.isSolverCrashed()) {
				mTraceCheckFinished = true;
				cleanupAndUnlockSolver();
			} else if (feasibilityResult.getReasonUnknown()
					.getExceptionHandlingCategory() != ExceptionHandlingCategory.KNOWN_IGNORE) {
				throw new AssertionError(feasibilityResult.getReasonUnknown().getException());
			}
		} catch (final ToolchainCanceledException e) {
			feasibilityResult = new FeasibilityCheckResult(LBool.UNKNOWN,
					new TraceCheckReasonUnknown(Reason.ULTIMATE_TIMEOUT, e, ExceptionHandlingCategory.KNOWN_IGNORE),
					false);
		} catch (final SMTLIBException e) {
			feasibilityResult =
					new FeasibilityCheckResult(LBool.UNKNOWN, TraceCheckReasonUnknown.constructReasonUnknown(e), true);
		} catch (final InnerTraceCheckException e) {
			feasibilityResult =
					new FeasibilityCheckResult(LBool.UNKNOWN, e.getTraceCheckReasonUnknown(), e.hasSolverCrashed());
		} catch (final Exception e) {
			feasibilityResult = new FeasibilityCheckResult(LBool.UNKNOWN,
					new TraceCheckReasonUnknown(Reason.SOLVER_CRASH_OTHER, e, ExceptionHandlingCategory.UNKNOWN), true);
		} finally {
			mFeasibilityResult = feasibilityResult;
			mProvidesIcfgProgramExecution = providesIcfgProgramExecution;
			mRcfgProgramExecution = icfgProgramExecution;
			mTraceCheckFinished = true;
		}
	}

	/**
	 * Create new trace check with a fresh solver and default settings.
	 *
	 * @param services
	 */
	public static TraceCheck<IAction> createTraceCheck(final IUltimateServiceProvider services,
			final CfgSmtToolkit toolkit, final ManagedScript mgdScriptTc, final IPredicate pre, final IPredicate post,
			final List<? extends IAction> trace) {
		final SortedMap<Integer, IPredicate> pendingContexts = new TreeMap<>();
		final NestedWord<IAction> nw = NestedWord.nestedWord(new Word<>(trace.toArray(new IAction[trace.size()])));
		final NestedFormulas<IAction, UnmodifiableTransFormula, IPredicate> rv =
				new DefaultTransFormulas<>(nw, pre, post, pendingContexts, toolkit.getOldVarsAssignmentCache(), false);
		final AssertCodeBlockOrder acbo = new AssertCodeBlockOrder(AssertCodeBlockOrderType.NOT_INCREMENTALLY);
		final boolean computeRcfgProgramExecution = true;
		final boolean collectInterpolatSequenceStatistics = false;
		final boolean unlockSmtSolverAlsoIfUnsat = true;
		return new TraceCheck<>(pre, post, pendingContexts, nw, rv, services, toolkit, mgdScriptTc, acbo,
				computeRcfgProgramExecution, collectInterpolatSequenceStatistics, unlockSmtSolverAlsoIfUnsat);
	}

	@Override
	public LBool isCorrect() {
		return mFeasibilityResult.getLBool();
	}

	@Override
	public TraceCheckReasonUnknown getTraceCheckReasonUnknown() {
		if (isCorrect() == LBool.UNKNOWN) {
			return mFeasibilityResult.getReasonUnknown();
		}
		throw new IllegalStateException("only available trace feasibility result is unknown.");
	}

	/**
	 * Like three-argument-checkTrace-Method above but for traces which contain pending returns. The pendingContext maps
	 * the positions of pending returns to predicates which define possible variable valuations in the context to which
	 * the return leads the trace.
	 */
	protected FeasibilityCheckResult checkTrace() {
		lockAndPrepareSolverForTraceCheck();
		mTraceCheckBenchmarkGenerator.start(TraceCheckStatisticsDefinitions.SsaConstructionTime.toString());
		mNsb = new NestedSsaBuilder<>(mTrace, mTcSmtManager, mCsToolkit, mNestedFormulas, mLogger);
		final NestedFormulas<L, Term, Term> ssa = mNsb.getSsa();
		mTraceCheckBenchmarkGenerator.stop(TraceCheckStatisticsDefinitions.SsaConstructionTime.toString());

		mTraceCheckBenchmarkGenerator.start(TraceCheckStatisticsDefinitions.SatisfiabilityAnalysisTime.toString());
		if (mAssertCodeBlockOrder.getAssertCodeBlockOrderType() != AssertCodeBlockOrderType.NOT_INCREMENTALLY) {
			mAAA = new AnnotateAndAsserterWithStmtOrderPrioritization<>(mTcSmtManager, ssa,
					getAnnotateAndAsserterCodeBlocks(ssa), mTraceCheckBenchmarkGenerator, mAssertCodeBlockOrder,
					mServices);
		} else {
			mAAA = new AnnotateAndAsserter<>(mTcSmtManager, ssa, getAnnotateAndAsserterCodeBlocks(ssa),
					mTraceCheckBenchmarkGenerator, mServices);
			// Report the asserted code blocks
			// mTraceCheckBenchmarkGenerator.reportnewAssertedCodeBlocks(mTrace.length());
		}
		FeasibilityCheckResult result = null;
		try {
			mAAA.buildAnnotatedSsaAndAssertTerms();
			final LBool isSafe = mAAA.isInputSatisfiable();
			TraceCheckReasonUnknown tcru;
			if (isSafe == LBool.UNKNOWN) {
				tcru = new TraceCheckReasonUnknown(Reason.SOLVER_RESPONSE_OTHER, null, null);
			} else {
				tcru = null;
			}
			result = new FeasibilityCheckResult(isSafe, tcru, false);
		} catch (final SMTLIBException e) {
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				// there was a cancellation request, probably responsible for
				// abnormal solver termination
				result = new FeasibilityCheckResult(LBool.UNKNOWN, new TraceCheckReasonUnknown(Reason.ULTIMATE_TIMEOUT,
						null, ExceptionHandlingCategory.KNOWN_IGNORE), true);
			} else {
				result = new FeasibilityCheckResult(LBool.UNKNOWN, TraceCheckReasonUnknown.constructReasonUnknown(e),
						true);
			}
		} finally {
			mTraceCheckBenchmarkGenerator.stop(TraceCheckStatisticsDefinitions.SatisfiabilityAnalysisTime.toString());
		}
		return result;
	}

	/**
	 * Compute a program execution for the checked trace. If the checked trace violates its specification (result of
	 * trace check is SAT), we compute a program execution that contains program states that witness the violation of
	 * the specification (however, this can still be partial program states e.g., no values assigned to arrays) and that
	 * contains information which branch of a parallel composed CodeBlock violates the specification.
	 *
	 * @param managedScriptTc
	 *
	 * @return
	 */
	private IcfgProgramExecution<L> computeRcfgProgramExecutionAndDecodeBranches(final ManagedScript managedScriptTc) {
		if (!(mNestedFormulas instanceof DefaultTransFormulas)
				|| !((DefaultTransFormulas<L>) mNestedFormulas).hasBranchEncoders()) {
			final String msg = "Trace is feasible, we will do another trace check, this time with branch encoders.";
			managedScriptTc.echo(mTraceCheckLock, new QuotedObject(msg));
			mLogger.info(msg);
			cleanupAndUnlockSolver();
			final DefaultTransFormulas<L> withBE = new DefaultTransFormulas<>(mNestedFormulas.getTrace(),
					mNestedFormulas.getPrecondition(), mNestedFormulas.getPostcondition(), mPendingContexts,
					mCsToolkit.getOldVarsAssignmentCache(), true);
			final TraceCheck<L> tc = new TraceCheck<>(mNestedFormulas.getPrecondition(),
					mNestedFormulas.getPostcondition(), mPendingContexts, mNestedFormulas.getTrace(), withBE, mServices,
					mCsToolkit, mTcSmtManager, AssertCodeBlockOrder.NOT_INCREMENTALLY, true, false, true);

			switch (tc.isCorrect()) {
			case SAT:
				return tc.getRcfgProgramExecution();
			case UNKNOWN:
				final Exception ex = tc.getTraceCheckReasonUnknown().getException();
				if (ex instanceof ToolchainCanceledException || ex instanceof AutomataOperationCanceledException) {
					// TODO: 20210701 DD: It might be useful to set a higher
					// timeout for a TraceCheck here because the
					// chance of getting a program execution if the previous TC
					// was already successful is high.
					throw new ToolchainCanceledException((IRunningTaskStackProvider) ex,
							new RunningTaskInfo(getClass(), "computing program execution"));
				}
				throw new InnerTraceCheckException("Exception in inner trace check during branch decoding",
						tc.getTraceCheckReasonUnknown(), tc.mFeasibilityResult.mSolverCrashed);
			case UNSAT:
				throw new AssertionError("result of second trace check is not SAT, but " + tc.isCorrect());
			default:
				throw new UnsupportedOperationException("unknown trace check result type:" + tc.isCorrect());
			}

		}
		return computeRcfgProgramExecution(mNsb);
	}

	/**
	 * Compute program execution in the case that the checked specification is violated (result of trace check is SAT).
	 */
	private IcfgProgramExecution<L> computeRcfgProgramExecution(final NestedSsaBuilder<L> nsb) {
		final RelevantVariables<L> relVars =
				new RelevantVariables<>(mNestedFormulas, mCsToolkit.getModifiableGlobalsTable());
		final IcfgProgramExecutionBuilder<L> rpeb =
				new IcfgProgramExecutionBuilder<>(mCsToolkit.getModifiableGlobalsTable(), mTrace, relVars);
		for (int i = 0; i < mTrace.length(); i++) {
			if (mTrace.getSymbol(i) instanceof IActionWithBranchEncoders) {
				final IActionWithBranchEncoders cb = (IActionWithBranchEncoders) mTrace.getSymbol(i);
				final UnmodifiableTransFormula tf = cb.getTransitionFormulaWithBranchEncoders();
				if (!tf.getBranchEncoders().isEmpty()) {
					final Map<TermVariable, Boolean> beMapping = new HashMap<>();
					for (final TermVariable tv : tf.getBranchEncoders()) {
						final String nameOfConstant = NestedSsaBuilder.branchEncoderConstantName(tv, i);
						final Term indexedBe = mTcSmtManager.getScript().term(nameOfConstant);
						final Term value = getValue(indexedBe);
						final Boolean booleanValue = getBooleanValue(value);
						beMapping.put(tv, booleanValue);
					}
					rpeb.setBranchEncoders(i, beMapping);
				}
			}
		}

		final Function<Term, Term> funGetValue;
		if (mCfgManagedScript != mTcSmtManager) {
			funGetValue = a -> new TermTransferrer(mTcSmtManager.getScript(), mCfgManagedScript.getScript())
					.transform(getValue(a));
		} else {
			funGetValue = this::getValue;
		}

		final TestVector testV = new TestVector();

		for (final var entry : nsb.getIndexedVarRepresentative().entrySet()) {
			final IProgramVar bv = entry.getKey();
			final Map<Integer, Term> indexedRepresentatives = entry.getValue();
			if (SmtUtils.isSortForWhichWeCanGetValues(bv.getTermVariable().getSort())) {
				boolean firstRepresentatives = true;
				for (final var representative : indexedRepresentatives.entrySet()) {
					final Integer index = representative.getKey();
					final Term indexedVar = representative.getValue();
					final Term valueT = funGetValue.apply(indexedVar);
					if (indexedVar instanceof ApplicationTerm) {
						assert ((ApplicationTerm) indexedVar).getParameters().length == 0;
						if (indexedVar.toStringDirect().contains("nondet") && firstRepresentatives) {
							assert indexedRepresentatives.entrySet().size() == 2;
							// TODO Not sure if save, but by far the best solution
							testV.addValueAssignment(valueT, index); // Only if nondetINT!!
							firstRepresentatives = false;
						}

					}
					rpeb.addValueAtVarAssignmentPosition(bv, index, valueT);

				}
			}
		}

		try {
			final boolean mExportTestCase = true; // TODO Setting
			if (!testV.isEmpty() && mExportTestCase) {
				TestExporter.getInstance().exportTests(testV, rpeb.mTrace.hashCode());
			}

		} catch (final Exception e) {
			// TODO TestGeneration Auto-generated catch block
			e.printStackTrace();
		}

		cleanupAndUnlockSolver();
		return rpeb.getIcfgProgramExecution();
	}

	protected AnnotateAndAssertCodeBlocks<L> getAnnotateAndAsserterCodeBlocks(final NestedFormulas<L, Term, Term> ssa) {
		return new AnnotateAndAssertCodeBlocks<>(mTcSmtManager, mTraceCheckLock, ssa, mLogger);
	}

	private Term getValue(final Term term) {
		return SmtUtils.getValues(mTcSmtManager.getScript(), Collections.singleton(term)).get(term);
	}

	private static Boolean getBooleanValue(final Term term) {
		Boolean result;
		if (SmtUtils.isTrueLiteral(term)) {
			result = Boolean.TRUE;
		} else if (SmtUtils.isFalseLiteral(term)) {
			result = Boolean.FALSE;
		} else {
			throw new AssertionError();
		}
		return result;
	}

	public List<L> getTrace() {
		return mTrace.asList();
	}

	@Override
	public IPredicate getPrecondition() {
		return mPrecondition;
	}

	@Override
	public IPredicate getPostcondition() {
		return mPostcondition;
	}

	@Override
	public Map<Integer, IPredicate> getPendingContexts() {
		return mPendingContexts;
	}

	@Override
	public boolean providesRcfgProgramExecution() {
		return mProvidesIcfgProgramExecution;
	}

	@Override
	public IcfgProgramExecution<L> getRcfgProgramExecution() {
		if (mRcfgProgramExecution == null) {
			throw new AssertionError("program execution has not yet been computed");
		}
		return mRcfgProgramExecution;
	}

	@Override
	public TraceCheckStatisticsGenerator getStatistics() {
		if (mTraceCheckFinished) {
			return mTraceCheckBenchmarkGenerator;
		} else {
			throw new IllegalStateException("Cannot obtain statistics from unfinished TraceCheck");
		}
	}

	private void lockAndPrepareSolverForTraceCheck() {
		mTcSmtManager.lock(mTraceCheckLock);
		mTcSmtManager.echo(mTraceCheckLock, new QuotedObject("starting trace check"));
		mTcSmtManager.push(mTraceCheckLock, 1);
	}

	protected void cleanupAndUnlockSolver() {
		mTcSmtManager.echo(mTraceCheckLock, new QuotedObject("finished trace check"));
		mTcSmtManager.pop(mTraceCheckLock, 1);
		mTcSmtManager.unlock(mTraceCheckLock);
	}

	/**
	 * Package private class used by trace checker to lock the {@link ManagedScript}.
	 */
	static class TraceCheckLock {
		// this abomination helps Matthias debug
	}

	/**
	 * @return true iff trace check was successfully finished. Examples for a not successfully finished trace check are:
	 *         Crash of solver, Toolchain cancelled,
	 */
	@Override
	public boolean wasTracecheckFinishedNormally() {
		return mTraceCheckFinished;
	}

	static class FeasibilityCheckResult {
		private final LBool mLBool;
		private final TraceCheckReasonUnknown mReasonUnknown;
		private final boolean mSolverCrashed;

		public FeasibilityCheckResult(final LBool lBool, final TraceCheckReasonUnknown reasonUnknown,
				final boolean solverCrashed) {
			assert lBool != LBool.UNKNOWN
					|| reasonUnknown != null : "if result is unknown you have to specify a reason";
			assert lBool == LBool.UNKNOWN
					|| reasonUnknown == null : "if result sat/unsat you cannot specify reason for unknown";
			mLBool = lBool;
			mReasonUnknown = reasonUnknown;
			mSolverCrashed = solverCrashed;
		}

		public LBool getLBool() {
			return mLBool;
		}

		public TraceCheckReasonUnknown getReasonUnknown() {
			return mReasonUnknown;
		}

		public boolean isSolverCrashed() {
			return mSolverCrashed;
		}
	}

	private static final class InnerTraceCheckException extends RuntimeException {

		private static final long serialVersionUID = 1L;
		private final transient TraceCheckReasonUnknown mTCRU;
		private final transient boolean mSolverCrashed;

		public InnerTraceCheckException(final String msg, final TraceCheckReasonUnknown traceCheckReasonUnknown,
				final boolean solverCrashed) {
			super(msg);
			mTCRU = traceCheckReasonUnknown;
			mSolverCrashed = solverCrashed;
		}

		public TraceCheckReasonUnknown getTraceCheckReasonUnknown() {
			return mTCRU;
		}

		public boolean hasSolverCrashed() {
			return mSolverCrashed;
		}
	}
}
