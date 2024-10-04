/*
 * Copyright (C) 2013-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus.ItpErrorStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.UnsatCores;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.ContainsQuantifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.predicates.IterativePredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.predicates.IterativePredicateTransformer.IPredicatePostprocessor;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.predicates.IterativePredicateTransformer.TraceInterpolationException;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.predicates.IterativePredicateTransformer.TraceInterpolationException.Reason;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckStatisticsGenerator.InterpolantType;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Use unsat core, predicate transformer and live variable analsysis to compute a sequence of interpolants.
 *
 * @author Betim Musa, Matthias Heizmann
 */
public class TraceCheckSpWp<L extends IAction> extends InterpolatingTraceCheck<L> {
	// Forward relevant predicates
	protected List<IPredicate> mInterpolantsFp;
	// Backward relevant predicates
	protected List<IPredicate> mInterpolantsBp;

	private final UnsatCores mUnsatCores;
	private final boolean mLiveVariables;
	private static final boolean USE_LIVE_VARIABLES_INSTEAD_OF_RELEVANT_VARIABLES = false;

	// We may post-process the forwards predicates, after the backwards predicates has been computed in order
	// to potentially eliminate quantifiers. The idea is the following:
	// If there is a predicate p in the forwards predicates that contains quantifiers and there is an equivalent
	// predicate p' in the backwards
	// predicates that is quantifier-free, then we may replace p by p'.
	private static final boolean POST_PROCESS_FP_PREDICATES = false;

	private final boolean mConstructForwardInterpolantSequence;
	/**
	 * Enables a check that is only useful for non-interprocedural sequences
	 */
	private static final boolean DEBUG_CHECK_SP_IMPLIES_WP = false;

	private enum ConstructBackwardSequence {
		YES, NO, IF_FP_WAS_NOT_PERFECT
	}

	private final ConstructBackwardSequence mConstructBackwardInterpolantSequence;

	private AnnotateAndAssertConjunctsOfCodeBlocks<L> mAnnotateAndAsserterConjuncts;
	private final InterpolantComputationStatus mInterpolantComputationStatus;

	private int mNonLiveVariablesFp = 0;
	private int mNonLiveVariablesBp = 0;
	private boolean mPerfectForwardSequence;
	private boolean mPerfectBackwardSequence;
	private boolean mAlternatingQuantifierBailout;

	public TraceCheckSpWp(final IPredicate precondition, final IPredicate postcondition,
			final SortedMap<Integer, IPredicate> pendingContexts, final NestedWord<L> trace,
			final CfgSmtToolkit csToolkit, final AssertCodeBlockOrder assertCodeBlockOrder, final UnsatCores unsatCores,
			final boolean useLiveVariables, final IUltimateServiceProvider services,
			final boolean computeRcfgProgramExecution, final PredicateFactory predicateFactory,
			final IPredicateUnifier predicateUnifier, final InterpolationTechnique interpolation,
			final ManagedScript mgdScriptTc, final SimplificationTechnique simplificationTechnique,
			final List<? extends Object> controlLocationSequence, final boolean collectInterpolatSequenceStatistics) {
		// superclass does feasibility check
		super(precondition, postcondition, pendingContexts, trace, controlLocationSequence, services, csToolkit,
				mgdScriptTc, predicateFactory, predicateUnifier, assertCodeBlockOrder, computeRcfgProgramExecution,
				collectInterpolatSequenceStatistics, simplificationTechnique);
		mUnsatCores = unsatCores;
		mLiveVariables = useLiveVariables;
		switch (interpolation) {
		case ForwardPredicates:
			mConstructForwardInterpolantSequence = true;
			mConstructBackwardInterpolantSequence = ConstructBackwardSequence.NO;
			mAlternatingQuantifierBailout = false;
			break;
		case BackwardPredicates:
			mConstructForwardInterpolantSequence = false;
			mConstructBackwardInterpolantSequence = ConstructBackwardSequence.YES;
			mAlternatingQuantifierBailout = false;
			break;
		case FPandBP:
			mConstructForwardInterpolantSequence = true;
			mConstructBackwardInterpolantSequence = ConstructBackwardSequence.YES;
			mAlternatingQuantifierBailout = false;
			break;
		case FPandBPonlyIfFpWasNotPerfect:
			mConstructForwardInterpolantSequence = true;
			mConstructBackwardInterpolantSequence = ConstructBackwardSequence.IF_FP_WAS_NOT_PERFECT;
			mAlternatingQuantifierBailout = true;
			break;
		default:
			throw new UnsupportedOperationException("unsupportedInterpolation");
		}
		final LBool result = isCorrect();
		if (result == LBool.UNSAT) {
			InterpolantComputationStatus actualInterpolationComputationStatus = null;
			try {
				computeInterpolants(new AllIntegers(), interpolation);
				actualInterpolationComputationStatus = new InterpolantComputationStatus();
			} catch (final ToolchainCanceledException ex) {
				throw ex;
			} catch (final Throwable ex) {
				actualInterpolationComputationStatus =
						new InterpolantComputationStatus(ItpErrorStatus.SMT_SOLVER_CRASH, ex);
			}
			mInterpolantComputationStatus = actualInterpolationComputationStatus;
		} else if (result == LBool.SAT) {
			mInterpolantComputationStatus = new InterpolantComputationStatus(ItpErrorStatus.TRACE_FEASIBLE, null);
		} else {
			mInterpolantComputationStatus =
					new InterpolantComputationStatus(ItpErrorStatus.SMT_SOLVER_CANNOT_INTERPOLATE_INPUT, null);
		}
	}

	@Override
	public void computeInterpolants(final Set<Integer> interpolatedPositions,
			final InterpolationTechnique interpolation) {
		mTraceCheckBenchmarkGenerator.start(TraceCheckStatisticsDefinitions.InterpolantComputationTime.toString());
		try {
			computeInterpolantsUsingUnsatCore(interpolatedPositions);
		} finally {
			mTraceCheckBenchmarkGenerator.stop(TraceCheckStatisticsDefinitions.InterpolantComputationTime.toString());
		}
		mTraceCheckFinished = true;
	}

	public boolean wasForwardPredicateComputationRequested() {
		return mConstructForwardInterpolantSequence;
	}

	public boolean wasBackwardsPredicatesComputationRequested() {
		return mConstructBackwardInterpolantSequence == ConstructBackwardSequence.YES
				|| mConstructBackwardInterpolantSequence == ConstructBackwardSequence.IF_FP_WAS_NOT_PERFECT
						&& !isForwardSequencePerfect();
	}

	public boolean wasBackwardSequenceConstructed() {
		return mInterpolantsBp != null;
	}

	public List<IPredicate> getForwardPredicates() {
		assert mInterpolantsFp != null : "Forwards predicates not computed!";
		return mInterpolantsFp;
	}

	public TracePredicates getForwardIpp() {
		return new TracePredicates(getPrecondition(), getPostcondition(), getForwardPredicates());
	}

	public List<IPredicate> getBackwardPredicates() {
		assert mInterpolantsBp != null : "Backwards predicates not computed!";
		return mInterpolantsBp;
	}

	public TracePredicates getBackwardIpp() {
		return new TracePredicates(getPrecondition(), getPostcondition(), getBackwardPredicates());
	}

	/***
	 * Computes predicates (interpolants) for the statements of an infeasible trace specified by the given set.
	 * Depending on settings, there are only forward predicates, or only backward predicates or both of them computed
	 * {@see computeForwardRelevantPredicates, computeBackwardRelevantPredicates} <br>
	 * The predicates are computed using an unsatisfiable core of the corresponding infeasibility proof of the trace in
	 * the following way: <br>
	 * 1. Replace statements, which don't occur in the unsatisfiable core by the statement <code> assume(true) </code>
	 * <br>
	 * 2. Compute live variables. <br>
	 * 3. Compute predicates for the trace, where the non-relevant statements has been substituted by
	 * <code> assume(true) </code>.
	 *
	 * @see LiveVariables
	 * @see PredicateTransformer
	 */
	private void computeInterpolantsUsingUnsatCore(final Set<Integer> interpolatedPositions) {
		if (!(interpolatedPositions instanceof AllIntegers)) {
			throw new UnsupportedOperationException();
		}
		final Set<Term> unsatCore = new HashSet<>(Arrays.asList(mTcSmtManager.getScript().getUnsatCore()));
		// unsat core obtained. We now pop assertion stack of solver. This
		// allows us to use solver e.g. for simplifications
		cleanupAndUnlockSolver();

		{
			final int numberOfConjunctsInTrace = mAnnotateAndAsserterConjuncts.getAnnotated2Original().keySet().size();
			final int numberOfConjunctsInUnsatCore;
			if (mUnsatCores == UnsatCores.IGNORE) {
				numberOfConjunctsInUnsatCore = 0;
			} else {
				numberOfConjunctsInUnsatCore = unsatCore.size();
			}
			if (mLogger.isInfoEnabled()) {
				final String logMessage = "Trace formula consists of " + numberOfConjunctsInTrace + " conjuncts, "
						+ unsatCore.size() + " conjuncts are in the unsatisfiable core";
				// if 50% or more of all conjucts are in the unsat core we output a warning
				if (unsatCore.size() * 2 >= numberOfConjunctsInTrace) {
					mLogger.warn(logMessage);
				} else {
					mLogger.info(logMessage);
				}
			}
			mTraceCheckBenchmarkGenerator.setConjunctsInSSA(numberOfConjunctsInTrace, numberOfConjunctsInUnsatCore);
		}

		final NestedFormulas<L, UnmodifiableTransFormula, IPredicate> rtf = constructRelevantTransFormulas(unsatCore);
		assert stillInfeasible(rtf) : "incorrect Unsatisfiable Core! trace length " + mTrace.length()
				+ " unsat-core size " + unsatCore.size();

		final Set<IProgramVar>[] liveVariables;
		if (USE_LIVE_VARIABLES_INSTEAD_OF_RELEVANT_VARIABLES) {
			// computation of live variables whose input is the original trace
			final LiveVariables<L> lvar = new LiveVariables<>(mNsb.getVariable2Constant(),
					mNsb.getConstants2BoogieVar(), mNsb.getIndexedVarRepresentative());
			liveVariables = lvar.getLiveVariables();
		} else {
			// computation of live variables whose input takes the unsat core into a account (if applicable)
			final RelevantVariables<L> rvar = new RelevantVariables<>(rtf, mCsToolkit.getModifiableGlobalsTable());
			liveVariables = rvar.getRelevantVariables();
		}

		if (mConstructForwardInterpolantSequence) {
			mLogger.info("Computing forward predicates...");
			try {
				final List<IPredicatePostprocessor> postprocs = new ArrayList<>();
				if (mLiveVariables) {
					postprocs.add(new LiveVariablesPostprocessorForward(liveVariables));
				}
				postprocs.add(new IterativePredicateTransformer.QuantifierEliminationPostprocessor(mServices, mCfgManagedScript,
						mPredicateFactory, mSimplificationTechnique));
				postprocs.add(new UnifyPostprocessor(mPredicateUnifier));
				final IterativePredicateTransformer<L> spt = new IterativePredicateTransformer<>(mPredicateFactory,
						mCfgManagedScript, mCsToolkit.getModifiableGlobalsTable(), mServices, mTrace, mPrecondition,
						mPostcondition, mPendingContexts, null, mSimplificationTechnique, mBoogie2SmtSymbolTable);
				mInterpolantsFp = spt.computeStrongestPostconditionSequence(rtf, postprocs).getPredicates();
			} catch (final ToolchainCanceledException tce) {
				final String taskDescription = "constructing forward predicates";
				tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
				throw tce;
			}
			assert TraceCheckUtils.checkInterpolantsInductivityForward(mInterpolantsFp, mTrace, mPrecondition,
					mPostcondition, mPendingContexts, "FP", mCsToolkit, mLogger) : "invalid Hoare triple in FP";

			mTraceCheckBenchmarkGenerator.reportSequenceOfInterpolants(mInterpolantsFp, InterpolantType.Forward);
			mTraceCheckBenchmarkGenerator.reportNumberOfNonLiveVariables(mNonLiveVariablesFp, InterpolantType.Forward);
			mTraceCheckBenchmarkGenerator.reportInterpolantComputation();
			if (mControlLocationSequence != null) {
				final BackwardCoveringInformation bci = TraceCheckUtils.computeCoverageCapability(mServices,
						getForwardIpp(), mControlLocationSequence, mLogger, mPredicateUnifier);
				mPerfectForwardSequence = bci.getPotentialBackwardCoverings() == bci.getSuccessfullBackwardCoverings();
				if (mPerfectForwardSequence) {
					mTraceCheckBenchmarkGenerator.reportPerfectInterpolantSequences();
				}
				mTraceCheckBenchmarkGenerator.addBackwardCoveringInformation(bci);
			}
		}

		if (mConstructBackwardInterpolantSequence == ConstructBackwardSequence.IF_FP_WAS_NOT_PERFECT
				&& isForwardSequencePerfect()) {
			mLogger.info("Omiting computation of backward sequence because forward sequence was already perfect");
		}

		if (wasBackwardsPredicatesComputationRequested()) {
			mLogger.info("Computing backward predicates...");
			try {
				final List<IPredicatePostprocessor> postprocs = new ArrayList<>();
				if (mLiveVariables) {
					postprocs.add(new LiveVariablesPostprocessorBackward(liveVariables));
				}
				postprocs.add(new IterativePredicateTransformer.QuantifierEliminationPostprocessor(mServices, mCfgManagedScript,
						mPredicateFactory, mSimplificationTechnique));
				postprocs.add(new UnifyPostprocessor(mPredicateUnifier));
				final IterativePredicateTransformer<L> spt = new IterativePredicateTransformer<>(mPredicateFactory,
						mCfgManagedScript, mCsToolkit.getModifiableGlobalsTable(), mServices, mTrace, mPrecondition,
						mPostcondition, mPendingContexts, null, mSimplificationTechnique, mBoogie2SmtSymbolTable);
				mInterpolantsBp =
						spt.computeWeakestPreconditionSequence(rtf, postprocs, false, mAlternatingQuantifierBailout)
								.getPredicates();

				assert TraceCheckUtils.checkInterpolantsInductivityBackward(mInterpolantsBp, mTrace, mPrecondition,
						mPostcondition, mPendingContexts, "BP", mCsToolkit, mLogger,
						mCfgManagedScript) : "invalid Hoare triple in BP";

				mTraceCheckBenchmarkGenerator.reportSequenceOfInterpolants(mInterpolantsBp, InterpolantType.Backward);
				mTraceCheckBenchmarkGenerator.reportNumberOfNonLiveVariables(mNonLiveVariablesBp,
						InterpolantType.Backward);
				mTraceCheckBenchmarkGenerator.reportInterpolantComputation();
				if (mControlLocationSequence != null) {
					final BackwardCoveringInformation bci = TraceCheckUtils.computeCoverageCapability(mServices,
							getBackwardIpp(), mControlLocationSequence, mLogger, mPredicateUnifier);
					mPerfectBackwardSequence =
							bci.getPotentialBackwardCoverings() == bci.getSuccessfullBackwardCoverings();
					if (mPerfectBackwardSequence) {
						mTraceCheckBenchmarkGenerator.reportPerfectInterpolantSequences();
					}
					mTraceCheckBenchmarkGenerator.addBackwardCoveringInformation(bci);
				}
			} catch (final ToolchainCanceledException tce) {
				final String taskDescription = "constructing backward predicates";
				tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
				throw tce;
			} catch (final TraceInterpolationException e) {
				if (e.getReason() == Reason.ALTERNATING_QUANTIFIER_BAILOUT) {
					mInterpolantsBp = null;
				} else {
					throw new AssertionError("unknown reason", e);
				}
			}
		}

		if (mConstructForwardInterpolantSequence && wasBackwardSequenceConstructed() && POST_PROCESS_FP_PREDICATES) {
			for (int i = 0; i < mInterpolantsFp.size(); i++) {
				final IPredicate pOld = mInterpolantsFp.get(i);
				final IPredicate pNew = mPredicateUnifier.getOrConstructPredicate(pOld.getFormula());
				mInterpolantsFp.set(i, pNew);
			}
		}

		// Do some correctness test
		if (DEBUG_CHECK_SP_IMPLIES_WP && mConstructForwardInterpolantSequence && wasBackwardSequenceConstructed()) {
			checkSPImpliesWP(mInterpolantsFp, mInterpolantsBp);
		}

		if (mConstructForwardInterpolantSequence && wasBackwardSequenceConstructed()) {
			final boolean omitMixedSequence = true;
			if (omitMixedSequence) {
				mInterpolants = null;
			} else {
				selectListOFPredicatesFromBothTypes();
			}
		} else if (mConstructForwardInterpolantSequence) {
			mInterpolants = mInterpolantsFp.toArray(new IPredicate[mInterpolantsFp.size()]);
		} else if (wasBackwardSequenceConstructed()) {
			mInterpolants = mInterpolantsBp.toArray(new IPredicate[mInterpolantsBp.size()]);
		} else {
			throw new AssertionError("illegal choice");
		}
	}

	/**
	 * Construct representation of the trace formula that contains only the conjuncts that occur in the unsat core.
	 */
	private NestedFormulas<L, UnmodifiableTransFormula, IPredicate>
			constructRelevantTransFormulas(final Set<Term> unsatCore) {
		final NestedFormulas<L, UnmodifiableTransFormula, IPredicate> rtf;
		if (mUnsatCores == UnsatCores.IGNORE) {
			rtf = new DefaultTransFormulas<>(mTrace, mPrecondition, mPostcondition, mPendingContexts,
					mCsToolkit.getOldVarsAssignmentCache(), false);
		} else if (mUnsatCores == UnsatCores.STATEMENT_LEVEL) {
			final boolean[] localVarAssignmentAtCallInUnsatCore = new boolean[mTrace.length()];
			final boolean[] oldVarAssignmentAtCallInUnsatCore = new boolean[mTrace.length()];
			// Filter out the statements, which doesn't occur in the unsat core.
			final Set<L> codeBlocksInUnsatCore = filterOutIrrelevantStatements(mTrace, unsatCore,
					localVarAssignmentAtCallInUnsatCore, oldVarAssignmentAtCallInUnsatCore);
			rtf = new RelevantTransFormulas<>(mTrace, mPrecondition, mPostcondition, mPendingContexts,
					codeBlocksInUnsatCore, mCsToolkit.getOldVarsAssignmentCache(), localVarAssignmentAtCallInUnsatCore,
					oldVarAssignmentAtCallInUnsatCore, mCfgManagedScript);
		} else if (mUnsatCores == UnsatCores.CONJUNCT_LEVEL) {
			rtf = new RelevantTransFormulas<>(mNestedFormulas, mPrecondition, mPostcondition, mPendingContexts, unsatCore,
					mCsToolkit.getOldVarsAssignmentCache(), mCfgManagedScript, mAAA, mAnnotateAndAsserterConjuncts);
		} else {
			throw new AssertionError("unknown case:" + mUnsatCores);
		}
		return rtf;
	}

	/***
	 * Selects a list of predicates from the predicates computed via strongest post-condition and the weakest
	 * precondition, such that the number of predicates containing quantifiers is minimized and a mix-up of the two
	 * types is avoided. (If the predicates are mixed-up, they may get non-inductive.) Predicates are selected in the
	 * following way: (TODO:)
	 */
	private void selectListOFPredicatesFromBothTypes() {
		assert mInterpolantsFp.size() == mInterpolantsBp.size();
		mInterpolants = new IPredicate[mInterpolantsBp.size()];
		int i = 0; // position of predicate computed by strongest post-condition
		int j = mInterpolantsBp.size(); // position of predicate computed by
		// weakest precondition
		final ContainsQuantifier containsQuantifier = new ContainsQuantifier();
		while (i != j) {
			if (!containsQuantifier.containsQuantifier(mInterpolantsBp.get(j - 1).getFormula())) {
				mInterpolants[j - 1] = mInterpolantsBp.get(j - 1);
				j--;
			} else if (!containsQuantifier.containsQuantifier(mInterpolantsFp.get(i).getFormula())) {
				mInterpolants[i] = mInterpolantsFp.get(i);
				i++;
			} else {
				throw new UnsupportedOperationException("removed in refactoring");
				// 2016-05-05 Matthias: I deleted BasicPredicateExplicitQuantifier, hence
				// the following code does not compile any more
				// fix: Count quantified variables
				// int numOfQuantifiedVarsInFp = ((BasicPredicateExplicitQuantifier) mInterpolantsFp.get(i))
				// .getQuantifiedVariables().size();
				// int numOfQuantifiedVarsInBp = ((BasicPredicateExplicitQuantifier) mInterpolantsBp.get(j - 1))
				// .getQuantifiedVariables().size();
				// if (numOfQuantifiedVarsInFp < numOfQuantifiedVarsInBp) {
				// mInterpolants[i] = mInterpolantsFp.get(i);
				// i++;
				// } else {
				// mInterpolants[j - 1] = mInterpolantsBp.get(j - 1);
				// j--;
				// }
			}
		}
	}

	/**
	 * Checks whether the trace consisting of only relevant statements is still infeasible. This check is desired, when
	 * we use unsatisfiable cores of finer granularity.
	 *
	 * @return true iff result of infeasiblity check is unsat or unknown
	 */
	private boolean stillInfeasible(final NestedFormulas<L, UnmodifiableTransFormula, IPredicate> rv) {
		final TraceCheck<L> tc = new TraceCheck<>(rv.getPrecondition(), rv.getPostcondition(), new TreeMap<>(),
				rv.getTrace(), rv, mServices, mCsToolkit, AssertCodeBlockOrder.NOT_INCREMENTALLY, false, true, true);
		final boolean result = tc.isCorrect() != LBool.SAT;
		return result;
	}

	/**
	 * Select the statements from the given trace, which are contained in the unsatisfiable core. These statements
	 * contribute to the unsatisfiability of the trace, and therefore only these are important for the computations done
	 * afterwards.
	 */
	private Set<L> filterOutIrrelevantStatements(final NestedWord<L> trace, final Set<Term> unsatCoresAsSet,
			final boolean[] localVarAssignmentAtCallInUnsatCore, final boolean[] oldVarAssignmentAtCallInUnsatCore) {
		final Set<L> codeBlocksInUnsatCore = new HashSet<>();
		for (int i = 0; i < trace.length(); i++) {
			if (!trace.isCallPosition(i)
					&& unsatCoresAsSet.contains(mAAA.getAnnotatedSsa().getFormulaFromNonCallPos(i))) {
				codeBlocksInUnsatCore.add(trace.getSymbol(i));
			} else if (trace.isCallPosition(i)
					&& (unsatCoresAsSet.contains(mAAA.getAnnotatedSsa().getGlobalVarAssignment(i))
							|| unsatCoresAsSet.contains(mAAA.getAnnotatedSsa().getOldVarAssignment(i)))) {
				// The upper condition checks, whether the globalVarAssignments
				// is in unsat core, now check whether the local variable
				// assignments
				// is in unsat core, if it is Call statement
				if (unsatCoresAsSet.contains(mAAA.getAnnotatedSsa().getLocalVarAssignment(i))) {
					localVarAssignmentAtCallInUnsatCore[i] = true;
				}
				if (unsatCoresAsSet.contains(mAAA.getAnnotatedSsa().getOldVarAssignment(i))) {
					oldVarAssignmentAtCallInUnsatCore[i] = true;
				}
				// Add the globalVarAssignments to the unsat_core, if it is a
				// Call statement, otherwise it adds
				// the statement
				codeBlocksInUnsatCore.add(trace.getSymbol(i));
			} else {
				if (trace.getSymbol(i) instanceof ICallAction
						&& unsatCoresAsSet.contains(mAAA.getAnnotatedSsa().getLocalVarAssignment(i))) {
					localVarAssignmentAtCallInUnsatCore[i] = true;
				}
			}
		}
		return codeBlocksInUnsatCore;
	}

	public class LiveVariablesPostprocessorForward implements IPredicatePostprocessor {
		private final Set<IProgramVar>[] mRelevantVars;

		public LiveVariablesPostprocessorForward(final Set<IProgramVar>[] relevantVars) {
			mRelevantVars = relevantVars;
		}

		@Override
		public IPredicate postprocess(final IPredicate pred, final int i) {
			assert mLiveVariables : "use this postprocessor only if mLiveVariables";
			final Set<TermVariable> nonLiveVars = computeIrrelevantVariables(mRelevantVars[i], pred);
			final Term projectedT = SmtUtils.quantifier(mCfgManagedScript.getScript(), QuantifiedFormula.EXISTS,
					nonLiveVars, pred.getFormula());
			// apply only a parsimonious quantifier elimination,
			// we use a quantifier elimination postprocessor later
			final Term pushed = PartialQuantifierElimination.eliminateLight(mServices, mCfgManagedScript, projectedT);
			final IPredicate projected = mPredicateFactory.newPredicate(pushed);
			mNonLiveVariablesFp += nonLiveVars.size();
			return projected;
		}

	}

	public class LiveVariablesPostprocessorBackward implements IPredicatePostprocessor {
		private final Set<IProgramVar>[] mRelevantVars;

		public LiveVariablesPostprocessorBackward(final Set<IProgramVar>[] relevantVars) {
			super();
			mRelevantVars = relevantVars;
		}

		@Override
		public IPredicate postprocess(final IPredicate pred, final int i) {
			assert mLiveVariables : "use this postprocessor only if mLiveVariables";
			final Set<TermVariable> nonLiveVars = computeIrrelevantVariables(mRelevantVars[i], pred);
			final Term projectedT = SmtUtils.quantifier(mCfgManagedScript.getScript(), QuantifiedFormula.FORALL,
					nonLiveVars, pred.getFormula());
			// apply only a parsimonious quantifier elimination,
			// we use a quantifier elimination postprocessor later
			final Term pushed = PartialQuantifierElimination.eliminateLight(mServices, mCfgManagedScript, projectedT);
			final IPredicate projected = mPredicateFactory.newPredicate(pushed);
			mNonLiveVariablesBp += nonLiveVars.size();
			return projected;
		}
	}

	public static class UnifyPostprocessor implements IPredicatePostprocessor {

		private final IPredicateUnifier mPredicateUnifier;

		public UnifyPostprocessor(final IPredicateUnifier predicateUnifier) {
			mPredicateUnifier = predicateUnifier;
		}

		@Override
		public IPredicate postprocess(final IPredicate pred, final int i) {
			final IPredicate unified = mPredicateUnifier.getOrConstructPredicate(pred.getFormula());
			return unified;
		}
	}

	/**
	 * Compute the irrelevant variables of the given predicate p. A variable is irrelevant, if it isn't contained in the
	 * given set of relevantVars.
	 *
	 * @see LiveVariables
	 */
	private static Set<TermVariable> computeIrrelevantVariables(final Set<IProgramVar> relevantVars,
			final IPredicate p) {
		final Set<TermVariable> result = new HashSet<>();
		for (final IProgramVar bv : p.getVars()) {
			if (!relevantVars.contains(bv)) {
				result.add(bv.getTermVariable());
			}
		}
		return result;
	}

	/***
	 * Check for each predicate computed via the strongest post-condition, whether it implies the predicate computed via
	 * weakest precondition. This check is desired, when predicates are computed twice (once via strongest post, and
	 * once via weakest pre-condition). It ensures the correctness of the predicates.
	 */
	private void checkSPImpliesWP(final List<IPredicate> interpolantsFp, final List<IPredicate> interpolantsBp) {
		mLogger.debug("Checking implication of SP and WP...");
		final MonolithicImplicationChecker mic = new MonolithicImplicationChecker(mServices, mCfgManagedScript);
		for (int i = 0; i < interpolantsFp.size(); i++) {
			final Validity result = mic.checkImplication(interpolantsFp.get(i), false, interpolantsBp.get(i), false);
			mLogger.debug("SP {" + interpolantsFp.get(i) + "} ==> WP {" + interpolantsBp.get(i) + "} is "
					+ (result == Validity.VALID ? "valid" : result == Validity.INVALID ? "not valid" : result));
			assert result == Validity.VALID || result == Validity.UNKNOWN : "checkSPImpliesWP failed";
		}
	}

	@Override
	protected AnnotateAndAssertCodeBlocks<L> getAnnotateAndAsserterCodeBlocks(final NestedFormulas<L, Term, Term> ssa) {
		if (mAnnotateAndAsserterConjuncts == null) {
			mAnnotateAndAsserterConjuncts = new AnnotateAndAssertConjunctsOfCodeBlocks<>(mTcSmtManager, mTraceCheckLock,
					ssa, mNestedFormulas, mLogger, mCfgManagedScript);
		}
		return mAnnotateAndAsserterConjuncts;
	}

	public boolean isForwardSequencePerfect() {
		if (mInterpolantsFp == null) {
			throw new UnsupportedOperationException("forward sequence not constructed");
		}
		return mPerfectForwardSequence;
	}

	public boolean isBackwardSequencePerfect() {
		if (mInterpolantsBp == null) {
			throw new UnsupportedOperationException("backward sequence not constructed");
		}
		return mPerfectBackwardSequence;
	}

	@Override
	public InterpolantComputationStatus getInterpolantComputationStatus() {
		return mInterpolantComputationStatus;
	}

}
