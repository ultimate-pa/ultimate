/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus.ItpErrorStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrderType;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckStatisticsGenerator.InterpolantType;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

/**
 * Uses Craig interpolation for computation of nested interpolants. Supports two algorithms. 1. Matthias' recursive
 * algorithm. 2. Tree interpolation
 *
 * @author heizmann@informatik.uni-freiburg.de
 */
public class InterpolatingTraceCheckCraig<L extends IAction> extends InterpolatingTraceCheck<L> {

	private final boolean mInstantiateArrayExt;
	private final InterpolantComputationStatus mInterpolantComputationStatus;

	/**
	 * Check if trace fulfills specification given by precondition, postcondition and pending contexts. The
	 * pendingContext maps the positions of pending returns to predicates which define possible variable valuations in
	 * the context to which the return leads the trace.
	 */
	public InterpolatingTraceCheckCraig(final IPredicate precondition, final IPredicate postcondition,
			final SortedMap<Integer, IPredicate> pendingContexts, final NestedWord<L> trace,
			final List<? extends Object> controlLocationSequence, final IUltimateServiceProvider services,
			final CfgSmtToolkit csToolkit, final ManagedScript mgdScriptTc, final PredicateFactory predicateFactory,
			final IPredicateUnifier predicateUnifier, final AssertCodeBlockOrder assertCodeBlockOrder,
			final boolean computeRcfgProgramExecution, final boolean collectInterpolantStatistics,
			final InterpolationTechnique interpolation, final boolean instanticateArrayExt,
			final XnfConversionTechnique xnfConversionTechnique, final SimplificationTechnique simplificationTechnique,
			final boolean innerRecursiveNestedInterpolationCall) {
		super(precondition, postcondition, pendingContexts, trace, controlLocationSequence, services, csToolkit,
				mgdScriptTc, predicateFactory, predicateUnifier, assertCodeBlockOrder, computeRcfgProgramExecution,
				collectInterpolantStatistics, simplificationTechnique, xnfConversionTechnique);
		if (assertCodeBlockOrder.getAssertCodeBlockOrderType() != AssertCodeBlockOrderType.NOT_INCREMENTALLY) {
			throw new UnsupportedOperationException("incremental assertion is not available for Craig interpolation");
		}
		mInstantiateArrayExt = instanticateArrayExt;
		if (isCorrect() == LBool.UNSAT) {
			InterpolantComputationStatus ics = new InterpolantComputationStatus();
			try {
				computeInterpolants(new AllIntegers(), interpolation);
				mTraceCheckBenchmarkGenerator.reportSequenceOfInterpolants(Arrays.asList(mInterpolants),
						InterpolantType.Craig);
				if (!innerRecursiveNestedInterpolationCall) {
					mTraceCheckBenchmarkGenerator.reportInterpolantComputation();
					if (mControlLocationSequence != null) {
						final BackwardCoveringInformation bci = TraceCheckUtils.computeCoverageCapability(mServices,
								getIpp(), mControlLocationSequence, mLogger, mPredicateUnifier);
						final boolean perfectSequence =
								bci.getPotentialBackwardCoverings() == bci.getSuccessfullBackwardCoverings();
						if (perfectSequence) {
							mTraceCheckBenchmarkGenerator.reportPerfectInterpolantSequences();
						}
						mTraceCheckBenchmarkGenerator.addBackwardCoveringInformation(bci);
					}
				}
			} catch (final UnsupportedOperationException e) {
				ics = handleUnsupportedOperationException(e);
			} catch (final SMTLIBException e) {
				ics = handleSmtLibException(e);
			} catch (final IllegalArgumentException e) {
				ics = handleIllegalArgumentException(e);
			} catch (final NestedTraceCheckException e) {
				ics = handleNestedTraceCheckException(e);
			}
			mTraceCheckFinished = true;
			mInterpolantComputationStatus = ics;
		} else if (isCorrect() == LBool.SAT) {
			mInterpolantComputationStatus = new InterpolantComputationStatus(ItpErrorStatus.TRACE_FEASIBLE, null);
		} else {
			mInterpolantComputationStatus =
					new InterpolantComputationStatus(ItpErrorStatus.SMT_SOLVER_CANNOT_INTERPOLATE_INPUT, null);
		}
	}

	public InterpolatingTraceCheckCraig(final IPredicate precondition, final IPredicate postcondition,
			final SortedMap<Integer, IPredicate> pendingContexts, final NestedWord<L> trace,
			final List<? extends Object> controlLocationSequence, final IUltimateServiceProvider services,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final IPredicateUnifier predicateUnifier, final AssertCodeBlockOrder assertCodeBlockOrder,
			final boolean computeRcfgProgramExecution, final boolean collectInterpolantStatistics,
			final InterpolationTechnique interpolation, final boolean instanticateArrayExt,
			final XnfConversionTechnique xnfConversionTechnique,
			final SimplificationTechnique simplificationTechnique) {
		this(precondition, postcondition, pendingContexts, trace, controlLocationSequence, services, csToolkit,
				csToolkit.getManagedScript(), predicateFactory, predicateUnifier, assertCodeBlockOrder,
				computeRcfgProgramExecution, collectInterpolantStatistics, interpolation, instanticateArrayExt,
				xnfConversionTechnique, simplificationTechnique, false);
	}

	private InterpolantComputationStatus handleNestedTraceCheckException(final NestedTraceCheckException e) {
		// unwrap nested exception and handle it here
		final Throwable cause = e.getCause();
		final InterpolantComputationStatus ics;
		if (cause instanceof UnsupportedOperationException) {
			ics = handleUnsupportedOperationException((UnsupportedOperationException) cause);
		} else if (cause instanceof SMTLIBException) {
			ics = handleSmtLibException((SMTLIBException) cause);
		} else if (cause instanceof IllegalArgumentException) {
			ics = handleIllegalArgumentException((IllegalArgumentException) cause);
		} else {
			throw e;
		}
		return ics;
	}

	private InterpolantComputationStatus handleUnsupportedOperationException(final UnsupportedOperationException e) {
		final String message = throwIfNoMessage(e);
		if (isMessageSolverCannotInterpolate(message)) {
			// SMTInterpol throws this during interpolation for unsupported fragments such as arrays
			return new InterpolantComputationStatus(ItpErrorStatus.SMT_SOLVER_CANNOT_INTERPOLATE_INPUT, e);
		}
		throw e;
	}

	private InterpolantComputationStatus handleSmtLibException(final SMTLIBException e) {
		final String message = throwIfNoMessage(e);
		if ("Unsupported non-linear arithmetic".equals(message)) {
			// SMTInterpol was somehow able to determine satisfiability but detects
			// non-linear arithmetic during interpolation
			return new InterpolantComputationStatus(ItpErrorStatus.SMT_SOLVER_CANNOT_INTERPOLATE_INPUT, e);
		}
		throw e;
	}

	private InterpolantComputationStatus handleIllegalArgumentException(final IllegalArgumentException e) {
		final String message = throwIfNoMessage(e);
		if (message.startsWith("Did not find overload for function =")) {
			// DD: this is a known bug in SMTInterpol; until it is fixed, we catch it here so that we can run
			// benchmarks
			return new InterpolantComputationStatus(ItpErrorStatus.SMT_SOLVER_CRASH, e);
		}
		throw e;
	}

	private String throwIfNoMessage(final RuntimeException e) {
		final String message = e.getMessage();
		if (message == null) {
			mLogger.fatal("Solver crashed with " + e.getClass().getSimpleName() + " whose message is null");
			throw e;
		}
		return message;
	}

	private static boolean isMessageSolverCannotInterpolate(final String message) {
		return message.startsWith("Cannot interpolate") || message.equals(NestedInterpolantsBuilder.DIFF_IS_UNSUPPORTED)
				|| message.startsWith("Unknown lemma type!");
	}

	/**
	 *
	 * @param interpolation
	 * @return
	 */
	protected int getTotalNumberOfPredicates(final InterpolationTechnique interpolation) {
		return mInterpolants != null ? mInterpolants.length : 0;
	}

	@Override
	protected void computeInterpolants(final Set<Integer> interpolatedPositions,
			final InterpolationTechnique interpolation) {
		mTraceCheckBenchmarkGenerator.start(TraceCheckStatisticsDefinitions.InterpolantComputationTime.toString());
		assert mPredicateUnifier != null;
		assert mPredicateUnifier.isRepresentative(mPrecondition);
		assert mPredicateUnifier.isRepresentative(mPostcondition);
		for (final IPredicate pred : mPendingContexts.values()) {
			assert mPredicateUnifier.isRepresentative(pred);
		}
		try {
			switch (interpolation) {
			case Craig_NestedInterpolation:
				computeInterpolantsRecursive(interpolatedPositions);
				break;
			case Craig_TreeInterpolation:
				computeInterpolantsTree(interpolatedPositions);
				break;
			default:
				throw new UnsupportedOperationException("unsupportedInterpolation");
			}
			mTraceCheckFinished = true;
		} catch (final ToolchainCanceledException tce) {
			final String taskDescription = "constructing Craig interpolants";
			tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
			throw tce;
		} finally {
			mTraceCheckBenchmarkGenerator.stop(TraceCheckStatisticsDefinitions.InterpolantComputationTime.toString());
		}
		// TODO: remove this if relevant variables are definitely correct.
		// assert testRelevantVars() : "bug in relevant variables";
	}

	private boolean testRelevantVars() {
		boolean result = true;
		final RelevantVariables rv = new RelevantVariables(mNestedFormulas, mCsToolkit.getModifiableGlobalsTable());
		for (int i = 0; i < mInterpolants.length; i++) {
			final IPredicate itp = mInterpolants[i];
			final Set<IProgramVar> vars = itp.getVars();
			final Set<IProgramVar> frel = rv.getForwardRelevantVariables()[i + 1];
			final Set<IProgramVar> brel = rv.getBackwardRelevantVariables()[i + 1];
			if (!frel.containsAll(vars)) {
				mLogger.warn("forward relevant variables wrong");
				result = false;
			}
			if (!brel.containsAll(vars)) {
				mLogger.warn("backward relevant variables wrong");
				result = false;
			}
		}
		return result;
	}

	@Override
	public IPredicate[] getInterpolants() {
		if (isCorrect() == LBool.UNSAT) {
			if (mInterpolants == null) {
				throw new AssertionError("No Interpolants");
			}
			assert mInterpolants.length == mTrace.length() - 1;
			return mInterpolants;
		}
		throw new UnsupportedOperationException("Interpolants are only available if trace is correct.");
	}

	@Override
	public InterpolantComputationStatus getInterpolantComputationStatus() {
		return mInterpolantComputationStatus;
	}

	/**
	 * Use tree interpolants to compute nested interpolants.
	 */
	private void computeInterpolantsTree(final Set<Integer> interpolatedPositions) {
		if (mFeasibilityResult.getLBool() != LBool.UNSAT) {
			throw new IllegalArgumentException("Interpolants only available if trace fulfills specification");
		}
		if (mInterpolants != null) {
			throw new AssertionError("You already computed interpolants");
		}
		final NestedInterpolantsBuilder<L> nib = new NestedInterpolantsBuilder<>(mTcSmtManager, mTraceCheckLock,
				mAAA.getAnnotatedSsa(), mNsb.getConstants2BoogieVar(), mPredicateUnifier, mPredicateFactory,
				interpolatedPositions, true, mServices, this, mCfgManagedScript, mInstantiateArrayExt,
				mSimplificationTechnique, mXnfConversionTechnique);
		mInterpolants = nib.getNestedInterpolants();
		assert TraceCheckUtils.checkInterpolantsInductivityForward(Arrays.asList(mInterpolants), mTrace, mPrecondition,
				mPostcondition, mPendingContexts, "Craig", mCsToolkit,
				mLogger) : "invalid Hoare triple in tree interpolants";
		assert mInterpolants != null;
	}

	/**
	 * Use Matthias' old naive iterative method to compute nested interpolants. (Recursive interpolation queries, one
	 * for each call-return pair)
	 */
	private void computeInterpolantsRecursive(final Set<Integer> interpolatedPositions) {
		assert interpolatedPositions != null : "no interpolatedPositions";
		if (mFeasibilityResult.getLBool() != LBool.UNSAT) {
			if (mFeasibilityResult.getLBool() == null) {
				throw new AssertionError("No trace check at the moment - no interpolants!");
			}
			throw new AssertionError("Interpolants only available if trace fulfills specification");
		}
		if (mInterpolants != null) {
			throw new AssertionError("You already computed interpolants");
		}

		final List<Integer> nonPendingCallPositions = new ArrayList<>();
		final Set<Integer> newInterpolatedPositions =
				interpolatedPositionsForSubtraces(interpolatedPositions, nonPendingCallPositions);

		final NestedInterpolantsBuilder<L> nib = new NestedInterpolantsBuilder<>(mTcSmtManager, mTraceCheckLock,
				mAAA.getAnnotatedSsa(), mNsb.getConstants2BoogieVar(), mPredicateUnifier, mPredicateFactory,
				newInterpolatedPositions, false, mServices, this, mCfgManagedScript, mInstantiateArrayExt,
				mSimplificationTechnique, mXnfConversionTechnique);
		mInterpolants = nib.getNestedInterpolants();
		final IPredicate oldPrecondition = mPrecondition;
		final IPredicate oldPostcondition = mPostcondition;

		for (final Integer nonPendingCall : nonPendingCallPositions) {
			// compute subtrace from to call to corresponding return
			final int returnPosition = mTrace.getReturnPosition(nonPendingCall);
			final NestedWord<L> subtrace = mTrace.getSubWord(nonPendingCall + 1, returnPosition);

			final IIcfgCallTransition<?> call = (IIcfgCallTransition<?>) mTrace.getSymbol(nonPendingCall);
			final String calledMethod = call.getSucceedingProcedure();
			final TermVarsProc oldVarsEquality = TraceCheckUtils.getOldVarsEquality(calledMethod,
					mCsToolkit.getModifiableGlobalsTable(), mCfgManagedScript.getScript());

			final IPredicate precondition = mPredicateUnifier.getOrConstructPredicate(oldVarsEquality.getFormula());

			// Use a pendingContext the interpolant at the position before the
			// call, if this is -1 (because call is first codeBlock) use the
			// precondition used in this recursive interpolant computation one
			// level above
			final SortedMap<Integer, IPredicate> pendingContexts = new TreeMap<>();
			IPredicate beforeCall;
			if (nonPendingCall == 0) {
				beforeCall = oldPrecondition;
			} else {
				beforeCall = mInterpolants[nonPendingCall - 1];
			}
			pendingContexts.put(subtrace.length() - 1, beforeCall);

			// Check if subtrace is "compatible" with interpolants computed so
			// far. Obviously trace fulfills specification, but we need this
			// proof to be able to compute interpolants.
			IPredicate interpolantAtReturnPosition;
			if (returnPosition == mTrace.length() - 1) {
				// special case: last position of trace is return
				// interpolant at this position is the postcondition
				// (which is stored in oldPostcondition, since mPostcondition
				// is already set to null.
				interpolantAtReturnPosition = oldPostcondition;
				assert interpolantAtReturnPosition != null;
			} else {
				interpolantAtReturnPosition = mInterpolants[returnPosition];
				assert interpolantAtReturnPosition != null;
			}

			mLogger.info("Compute interpolants for subsequence at non-pending call position " + nonPendingCall);
			// Compute interpolants for subsequence and add them to interpolants
			// computed by this traceCheck
			final InterpolatingTraceCheckCraig<L> tc = new InterpolatingTraceCheckCraig<>(precondition,
					interpolantAtReturnPosition, pendingContexts, subtrace, null, mServices, mCsToolkit, mTcSmtManager,
					mPredicateFactory, mPredicateUnifier, mAssertCodeBlockOrder, false,
					mTraceCheckBenchmarkGenerator.isCollectingInterpolantSequenceStatistics(),
					InterpolationTechnique.Craig_NestedInterpolation, mInstantiateArrayExt, mXnfConversionTechnique,
					mSimplificationTechnique, true);
			final LBool isSafe = tc.isCorrect();
			if (isSafe == LBool.SAT) {
				throw new AssertionError(
						"has to be unsat by construction, we do check only for interpolant computation");
			} else if (isSafe == LBool.UNKNOWN) {
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					throw new ToolchainCanceledException(this.getClass(), "construction of nested interpolants");

				}
				final TraceCheckReasonUnknown reasonsUnknown = tc.getTraceCheckReasonUnknown();
				throw new NestedTraceCheckException("UNKNOWN during nested interpolation. I don't know how to continue",
						reasonsUnknown.getException());
			}
			// tc.computeInterpolants_Recursive(interpolatedPositions, mPredicateUnifier);
			final IPredicate[] interpolantSubsequence = tc.getInterpolants();

			assert mPredicateFactory.isDontCare(mInterpolants[nonPendingCall]);
			mInterpolants[nonPendingCall] = precondition;
			for (int i = 0; i < interpolantSubsequence.length; i++) {
				assert mPredicateFactory.isDontCare(mInterpolants[nonPendingCall + 1 + i]);
				mInterpolants[nonPendingCall + 1 + i] = interpolantSubsequence[i];
			}
		}

		assert TraceCheckUtils.checkInterpolantsInductivityForward(Arrays.asList(mInterpolants), mTrace, mPrecondition,
				mPostcondition, mPendingContexts, "Craig", mCsToolkit,
				mLogger) : "invalid Hoare triple in nested interpolants";
	}

	/**
	 * Compute interpolated positions used in recursive interpolant computation
	 */
	private Set<Integer> interpolatedPositionsForSubtraces(final Set<Integer> interpolatedPositions,
			final List<Integer> nonPendingCallPositions) {

		final Set<Integer> newInterpolatedPositions = new HashSet<>();

		int currentContextStackDepth = 0;
		final NestedWord<?> nestedTrace = mTrace;
		for (int i = 0; i < nestedTrace.length() - 1; i++) {

			if (nestedTrace.isInternalPosition(i)) {
				if (interpolatedPositions.contains(i) && currentContextStackDepth == 0) {
					newInterpolatedPositions.add(i);
				}
			} else if (nestedTrace.isCallPosition(i)) {
				if (nestedTrace.isPendingCall(i)) {
					if (interpolatedPositions.contains(i) && currentContextStackDepth == 0) {
						newInterpolatedPositions.add(i);
					}
				} else {
					// we need interpolant before call if
					// currentContextStackDepth == 0
					if (currentContextStackDepth == 0) {
						nonPendingCallPositions.add(i);
					}
					currentContextStackDepth++;
					assert currentContextStackDepth > 0;
				}
			} else if (nestedTrace.isReturnPosition(i)) {
				currentContextStackDepth--;
				// new need interpolant after return if currentContextStackDepth
				// == 0
				if (currentContextStackDepth == 0) {
					newInterpolatedPositions.add(i);
				}
			} else {
				throw new AssertionError();
			}
		}
		return newInterpolatedPositions;
	}

	/**
	 * A {@link RuntimeException} that can be thrown when a nested trace check fails.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	private static final class NestedTraceCheckException extends RuntimeException {
		private static final long serialVersionUID = 1L;

		public NestedTraceCheckException(final String message, final Throwable cause) {
			super(message, cause);
		}
	}

}
