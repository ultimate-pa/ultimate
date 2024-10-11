/*
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2019 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.ExceptionHandlingCategory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult.BasicRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.Lazy;

/**
 * Checks a trace for feasibility and, if infeasible, constructs an interpolant automaton.
 *
 * @see IRefinementStrategy
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public final class AutomatonFreeRefinementEngine<L extends IIcfgTransition<?>>
		implements IRefinementEngine<L, Collection<QualifiedTracePredicates>> {

	private final ILogger mLogger;
	private final IRefinementStrategy<L> mStrategy;
	private final RefinementEngineStatisticsGenerator mRefinementEngineStatistics;

	private final LBool mFeasibility;
	private IProgramExecution<L, Term> mIcfgProgramExecution;
	private List<QualifiedTracePredicates> mUsedTracePredicates;
	private boolean mSomePerfectSequenceFound;
	private List<QualifiedTracePredicates> mQualifiedTracePredicates;

	private String mUsedTraceCheckFingerprint;
	private final IUltimateServiceProvider mServices;

	public AutomatonFreeRefinementEngine(final IUltimateServiceProvider services, final ILogger logger,
			final IRefinementStrategy<L> strategy) {
		mServices = services;
		mLogger = logger;
		mStrategy = strategy;
		mRefinementEngineStatistics = new RefinementEngineStatisticsGenerator();
		mFeasibility = executeStrategy();
		mRefinementEngineStatistics.finishRefinementEngineRun();
	}

	private IHoareTripleChecker getHoareTripleChecker() {
		final IHoareTripleChecker strategyHtc = mStrategy.getHoareTripleChecker(this);
		if (strategyHtc != null) {
			mLogger.info("Using hoare triple checker %s provided by strategy", strategyHtc.getClass().getSimpleName());
		}
		return strategyHtc;
	}

	private IPredicateUnifier getPredicateUnifier() {
		final IPredicateUnifier strategyUnifier = mStrategy.getPredicateUnifier(this);
		assert strategyUnifier != null;
		mLogger.info("Using predicate unifier %s provided by strategy %s", strategyUnifier.getClass().getSimpleName(),
				mStrategy.getName());
		return strategyUnifier;
	}

	@Override
	public RefinementEngineStatisticsGenerator getRefinementEngineStatistics() {
		return mRefinementEngineStatistics;
	}

	/**
	 * This method is the heart of the refinement engine.<br>
	 * It first checks feasibility of the counterexample. If infeasible, the method tries to find a perfect interpolant
	 * sequence. If unsuccessful, it collects all tested sequences. In the end an interpolant automaton is created.
	 *
	 * @return counterexample feasibility
	 */
	private LBool executeStrategy() {
		mLogger.info("Executing refinement strategy %s", mStrategy.getName());

		// first, check for feasibility
		final LBool feasibilityResult = checkFeasibility();
		if (feasibilityResult == LBool.UNKNOWN) {
			abortIfTimeout(String.format("Timeout during %s", mStrategy.getName()));
			mLogger.warn("Strategy %s was unsuccessful and could not determine trace feasibility", mStrategy.getName());
			return feasibilityResult;
		}

		// trace was feasible, return
		if (feasibilityResult == LBool.SAT) {
			mLogger.info("Strategy %s found a feasible trace", mStrategy.getName());
			return feasibilityResult;
		}

		// trace is infeasible, extract a proof
		if (feasibilityResult == LBool.UNSAT) {
			mLogger.info("Strategy %s found an infeasible trace", mStrategy.getName());
			return generateProof();
		}
		throw new UnsupportedOperationException("Unknown LBool: " + feasibilityResult);
	}

	private LBool generateProof() {
		final List<QualifiedTracePredicates> perfectIpps = new ArrayList<>();
		final List<QualifiedTracePredicates> imperfectIpps = new ArrayList<>();

		while (mStrategy.hasNextInterpolantGenerator(Collections.unmodifiableList(perfectIpps),
				Collections.unmodifiableList(imperfectIpps))) {
			final IIpgStrategyModule<?, L> interpolantGenerator = tryExecuteInterpolantGenerator();
			if (interpolantGenerator == null) {
				continue;
			}
			final Collection<QualifiedTracePredicates> newPeIpSeq =
					interpolantGenerator.getPerfectInterpolantSequences();
			perfectIpps.addAll(newPeIpSeq);
			final Collection<QualifiedTracePredicates> newImIpSeq =
					interpolantGenerator.getImperfectInterpolantSequences();
			imperfectIpps.addAll(newImIpSeq);
			mLogger.info("%s provided %s perfect and %s imperfect interpolant sequences",
					getModuleFingerprintString(interpolantGenerator), newPeIpSeq.size(), newImIpSeq.size());
			interpolantGenerator.aggregateStatistics(mRefinementEngineStatistics);
		}

		// strategy has finished providing interpolants, use them to construct the
		// interpolant automaton
		logStats(perfectIpps, imperfectIpps);
		if (!perfectIpps.isEmpty()) {
			mSomePerfectSequenceFound = true;
		}

		if (perfectIpps.isEmpty() && imperfectIpps.isEmpty()) {
			mLogger.error("Strategy %s failed to provide any proof altough trace is infeasible", mStrategy.getName());
			mQualifiedTracePredicates = null;
			return LBool.UNKNOWN;
		}
		mQualifiedTracePredicates = mStrategy.mergeInterpolants(perfectIpps, imperfectIpps);
		mUsedTracePredicates = mQualifiedTracePredicates;
		return LBool.UNSAT;
	}

	private void logStats(final List<QualifiedTracePredicates> perfectIpps,
			final List<QualifiedTracePredicates> imperfectIpps) {
		if (!mLogger.isInfoEnabled()) {
			return;
		}
		mLogger.info("Found %s perfect and %s imperfect interpolant sequences.", perfectIpps.size(),
				imperfectIpps.size());
		final List<Integer> numberInterpolantsPerfect = new ArrayList<>();
		final Set<IPredicate> allInterpolants = new HashSet<>();
		for (final QualifiedTracePredicates qtp : perfectIpps) {
			numberInterpolantsPerfect.add(new HashSet<>(qtp.getPredicates()).size());
			allInterpolants.addAll(qtp.getPredicates());
		}
		final List<Integer> numberInterpolantsImperfect = new ArrayList<>();
		for (final QualifiedTracePredicates qtp : imperfectIpps) {
			numberInterpolantsImperfect.add(new HashSet<>(qtp.getPredicates()).size());
			allInterpolants.addAll(qtp.getPredicates());
		}
		mLogger.info("Number of different interpolants: perfect sequences " + numberInterpolantsPerfect
				+ " imperfect sequences " + numberInterpolantsImperfect + " total " + allInterpolants.size());
	}

	private LBool checkFeasibility() {
		while (mStrategy.hasNextFeasilibityCheck()) {
			final ITraceCheckStrategyModule<L, ?> currentTraceCheck = mStrategy.nextFeasibilityCheck();
			abortIfTimeout("Timeout during feasibility check between " + mUsedTraceCheckFingerprint + " and "
					+ getModuleFingerprintString(currentTraceCheck));
			mUsedTraceCheckFingerprint = getModuleFingerprintString(currentTraceCheck);

			logModule("Using trace check", currentTraceCheck);
			final LBool feasibilityResult = currentTraceCheck.isCorrect();
			if (feasibilityResult == LBool.SAT) {
				if (currentTraceCheck.providesRcfgProgramExecution()) {
					mIcfgProgramExecution = currentTraceCheck.getRcfgProgramExecution();
				}
				currentTraceCheck.aggregateStatistics(mRefinementEngineStatistics);
				return feasibilityResult;
			}
			if (feasibilityResult == LBool.UNSAT) {
				currentTraceCheck.aggregateStatistics(mRefinementEngineStatistics);
				return feasibilityResult;
			}
			abortIfNecessaryOnUnknown(currentTraceCheck.getTraceCheckReasonUnknown());
			currentTraceCheck.aggregateStatistics(mRefinementEngineStatistics);
		}
		// no trace checker could determine the feasibility of the trace, need to abort
		return LBool.UNKNOWN;
	}

	private void abortIfTimeout(final String taskDesc) {
		if (!mServices.getProgressMonitorService().continueProcessing()) {
			throw new ToolchainCanceledException(getClass(), taskDesc);
		}
	}

	private void abortIfNecessaryOnUnknown(final TraceCheckReasonUnknown tcra) {
		if (tcra.getException() == null) {
			return;
		}

		final ExceptionHandlingCategory exceptionCategory = tcra.getExceptionHandlingCategory();
		switch (exceptionCategory) {
		case KNOWN_IGNORE:
		case KNOWN_DEPENDING:
		case KNOWN_THROW:
			if (mLogger.isErrorEnabled()) {
				mLogger.error("Caught known exception: " + tcra.getException().getMessage());
			}
			break;
		case UNKNOWN:
			if (mLogger.isErrorEnabled()) {
				mLogger.error("Caught unknown exception: " + tcra.getException().getMessage());
			}
			break;
		default:
			throw new IllegalArgumentException("Unknown exception category: " + exceptionCategory);
		}
		throwIfNecessary(tcra.getExceptionHandlingCategory(), tcra.getException());
	}

	private IIpgStrategyModule<?, L> tryExecuteInterpolantGenerator() {
		final IIpgStrategyModule<?, L> interpolantGenerator = mStrategy.nextInterpolantGenerator();
		abortIfTimeout(
				"Timeout during proof generation before using " + getModuleFingerprintString(interpolantGenerator));
		final InterpolantComputationStatus status;
		try {
			logModule("Using interpolant generator", interpolantGenerator);
			status = interpolantGenerator.getInterpolantComputationStatus();
			if (status == null) {
				mLogger.fatal("No interpolant computation status provided, assuming failure");
				throw new AssertionError(
						interpolantGenerator.getClass() + " provided no interpolant computation status");
			}
			if (status.wasComputationSuccessful()) {
				return interpolantGenerator;
			}
		} catch (final ToolchainCanceledException tce) {
			throw tce;
		} catch (final Exception e) {
			if (ExceptionHandlingCategory.UNKNOWN.throwException(mStrategy.getExceptionBlacklist())) {
				mLogger.fatal("Exception during interpolant generation: " + e.getClass().getSimpleName());
				throw e;
			}
			mLogger.fatal("Ignoring exception!", e);
			return null;
		}

		final ExceptionHandlingCategory category;
		switch (status.getStatus()) {
		case ALGORITHM_FAILED:
			category = ExceptionHandlingCategory.KNOWN_IGNORE;
			break;
		case OTHER:
			category = ExceptionHandlingCategory.UNKNOWN;
			break;
		case SMT_SOLVER_CANNOT_INTERPOLATE_INPUT:
			category = ExceptionHandlingCategory.KNOWN_IGNORE;
			break;
		case SMT_SOLVER_CRASH:
			category = ExceptionHandlingCategory.KNOWN_DEPENDING;
			break;
		case TRACE_FEASIBLE:
			final String msg = String.format("Tracecheck %s said UNSAT, interpolant generator %s failed with %s",
					mUsedTraceCheckFingerprint, getModuleFingerprintString(interpolantGenerator), status.getStatus());
			throw new IllegalStateException(msg);
		default:
			throw new AssertionError("unknown case : " + status.getStatus());
		}
		throwIfNecessary(category, status.getException());
		final String message =
				status.getException() == null ? String.valueOf(status.getStatus()) : status.getException().getMessage();
		mLogger.warn("Interpolation failed due to " + category + ": " + message);
		return null;
	}

	private void throwIfNecessary(final ExceptionHandlingCategory category, final Throwable t) {
		// note: you only need to use this function if you did not get the throwable
		// from a catch block!
		final boolean throwException = category.throwException(mStrategy.getExceptionBlacklist());
		if (throwException) {
			mLogger.warn("Global settings require throwing the following exception");
			// throw unchecked exceptions directly, wrap checked exceptions in
			// AssertionError
			if (t instanceof Error) {
				throw (Error) t;
			}
			if (t instanceof RuntimeException) {
				throw (RuntimeException) t;
			}
			throw new AssertionError(t);
		}
	}

	private void logModule(final String msg, final Object module) {
		mLogger.info("%s %s", msg, getModuleFingerprintString(module));
	}

	private static String getModuleFingerprintString(final Object obj) {
		return String.format("%s [%s]", obj.getClass().getSimpleName(), obj.hashCode());
	}

	@Override
	public IRefinementEngineResult<L, Collection<QualifiedTracePredicates>> getResult() {
		return new BasicRefinementEngineResult<>(mFeasibility, mQualifiedTracePredicates, mIcfgProgramExecution,
				mSomePerfectSequenceFound, mUsedTracePredicates, new Lazy<>(this::getHoareTripleChecker),
				new Lazy<>(this::getPredicateUnifier));
	}

}
