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

package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.ExceptionHandlingCategory;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;

/**
 * Checks a trace for feasibility and, if infeasible, constructs an interpolant automaton.
 *
 * This class is used in the {@link BasicCegarLoop}.
 *
 * @see IRefinementStrategy
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public final class TraceAbstractionRefinementEngine<LETTER extends IIcfgTransition<?>>
		implements IRefinementEngine<NestedWordAutomaton<LETTER, IPredicate>> {

	private final ILogger mLogger;
	private final IRefinementStrategy<LETTER> mStrategy;

	private final IPredicateUnifier mPredicateUnifier;
	private final Function<IPredicateUnifier, IHoareTripleChecker> mFunHtcConstructor;
	private final RefinementEngineStatisticsGenerator mRefinementEngineStatistics;

	private final LBool mFeasibility;
	private IProgramExecution<IIcfgTransition<IcfgLocation>, Term> mIcfgProgramExecution;
	private IHoareTripleChecker mHoareTripleChecker;
	private NestedWordAutomaton<LETTER, IPredicate> mInterpolantAutomaton;
	private boolean mSomePerfectSequenceFound;

	public TraceAbstractionRefinementEngine(final ILogger logger, final IPredicateUnifier predicateUnifier,
			final IRefinementStrategy<LETTER> strategy,
			final Function<IPredicateUnifier, IHoareTripleChecker> funHtcConstructor) {
		mLogger = logger;
		mPredicateUnifier = predicateUnifier;
		mStrategy = strategy;
		mFunHtcConstructor = funHtcConstructor;
		mRefinementEngineStatistics = new RefinementEngineStatisticsGenerator();
		mFeasibility = executeStrategy();
		mRefinementEngineStatistics.finishRefinementEngineRun();
	}

	@Override
	public LBool getCounterexampleFeasibility() {
		return mFeasibility;
	}

	@Override
	public NestedWordAutomaton<LETTER, IPredicate> getInfeasibilityProof() {
		return mInterpolantAutomaton;
	}

	@Override
	public boolean somePerfectSequenceFound() {
		return mSomePerfectSequenceFound;
	}

	@Override
	public boolean providesIcfgProgramExecution() {
		return mIcfgProgramExecution != null;
	}

	@Override
	public IProgramExecution<IIcfgTransition<IcfgLocation>, Term> getIcfgProgramExecution() {
		return mIcfgProgramExecution;
	}

	@Override
	public IHoareTripleChecker getHoareTripleChecker() {
		if (mHoareTripleChecker == null) {
			final IHoareTripleChecker strategyHtc = mStrategy.getHoareTripleChecker();
			if (strategyHtc == null) {
				mHoareTripleChecker = mFunHtcConstructor.apply(mPredicateUnifier);
			} else {
				mLogger.info("Using hoare triple checker %s provided by strategy",
						strategyHtc.getClass().getSimpleName());
				mHoareTripleChecker = strategyHtc;
			}
		}
		return mHoareTripleChecker;
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
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
			return generateProof();
		}
		throw new UnsupportedOperationException("Unknown LBool: " + feasibilityResult);
	}

	private LBool generateProof() {
		final List<TracePredicates> perfectIpps = new ArrayList<>();
		final List<TracePredicates> imperfectIpps = new ArrayList<>();

		while (mStrategy.hasNextInterpolantGenerator(perfectIpps, imperfectIpps)) {
			final IIpgStrategyModule<?, LETTER> interpolantGenerator = tryExecuteInterpolantGenerator();
			if (interpolantGenerator == null) {
				continue;
			}
			perfectIpps.addAll(interpolantGenerator.getPerfectInterpolantSequences());
			imperfectIpps.addAll(interpolantGenerator.getImperfectInterpolantSequences());
			interpolantGenerator.aggregateStatistics(mRefinementEngineStatistics);
		}

		// strategy has finished providing interpolants, use them to construct the interpolant automaton
		logStats(perfectIpps, imperfectIpps);
		if (!perfectIpps.isEmpty()) {
			mSomePerfectSequenceFound = true;
		}

		if (perfectIpps.isEmpty() && imperfectIpps.isEmpty()) {
			mLogger.error("Strategy %s failed to provide any proof altough trace is infeasible", mStrategy.getName());
			return LBool.UNKNOWN;
		}

		final IIpAbStrategyModule<LETTER> interpolantAutomatonBuilder = mStrategy.getInterpolantAutomatonBuilder();
		logModule("Using interpolant automaton builder", interpolantAutomatonBuilder);
		try {
			mInterpolantAutomaton = interpolantAutomatonBuilder.buildInterpolantAutomaton(perfectIpps, imperfectIpps);
		} catch (final AutomataOperationCanceledException e) {
			throw new ToolchainCanceledException(e,
					new RunningTaskInfo(interpolantAutomatonBuilder.getClass(), "computing interpolant automaton"));
		}
		return LBool.UNSAT;
	}

	private void logStats(final List<TracePredicates> perfectIpps, final List<TracePredicates> imperfectIpps) {
		if (!mLogger.isInfoEnabled()) {
			return;
		}
		mLogger.info("Constructing automaton from %s perfect and %s imperfect interpolant sequences.",
				perfectIpps.size(), imperfectIpps.size());
		final List<Integer> numberInterpolantsPerfect = new ArrayList<>();
		final Set<IPredicate> allInterpolants = new HashSet<>();
		for (final TracePredicates ipps : perfectIpps) {
			numberInterpolantsPerfect.add(new HashSet<>(ipps.getPredicates()).size());
			allInterpolants.addAll(ipps.getPredicates());
		}
		final List<Integer> numberInterpolantsImperfect = new ArrayList<>();
		for (final TracePredicates ipps : imperfectIpps) {
			numberInterpolantsImperfect.add(new HashSet<>(ipps.getPredicates()).size());
			allInterpolants.addAll(ipps.getPredicates());
		}
		mLogger.info("Number of different interpolants: perfect sequences " + numberInterpolantsPerfect
				+ " imperfect sequences " + numberInterpolantsImperfect + " total " + allInterpolants.size());
	}

	private LBool checkFeasibility() {
		while (mStrategy.hasNextFeasilibityCheck()) {
			final ITraceCheckStrategyModule<?> currentTraceCheck = mStrategy.nextFeasibilityCheck();
			logModule("Using trace check", currentTraceCheck);
			final LBool feasibilityResult = currentTraceCheck.isCorrect();
			if (feasibilityResult == LBool.SAT) {
				if (currentTraceCheck.providesRcfgProgramExecution()) {
					mIcfgProgramExecution = currentTraceCheck.getRcfgProgramExecution();
				}
				currentTraceCheck.aggregateStatistics(mRefinementEngineStatistics);
				return feasibilityResult;
			} else if (feasibilityResult == LBool.UNSAT) {
				currentTraceCheck.aggregateStatistics(mRefinementEngineStatistics);
				return feasibilityResult;
			}
			abortIfNecessaryOnUnknown(currentTraceCheck.getTraceCheckReasonUnknown());
			currentTraceCheck.aggregateStatistics(mRefinementEngineStatistics);
		}
		// no trace checker could determine the feasibility of the trace, need to abort
		return LBool.UNKNOWN;
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
		final boolean throwException =
				tcra.getExceptionHandlingCategory().throwException(mStrategy.getExceptionBlacklist());
		if (throwException) {
			if (mLogger.isInfoEnabled()) {
				mLogger.info("Global settings require throwing the exception.");
			}
			throw new AssertionError(tcra.getException());
		}
	}

	private IIpgStrategyModule<?, LETTER> tryExecuteInterpolantGenerator() {
		final InterpolantComputationStatus status;
		try {
			final IIpgStrategyModule<?, LETTER> interpolantGenerator = mStrategy.nextInterpolantGenerator();
			logModule("Using interpolant generator", interpolantGenerator);
			status = interpolantGenerator.getInterpolantComputationStatus();
			if (status.wasComputationSuccesful()) {
				return interpolantGenerator;
			}
		} catch (final ToolchainCanceledException tce) {
			throw tce;
		} catch (final Exception e) {
			if (ExceptionHandlingCategory.UNKNOWN.throwException(mStrategy.getExceptionBlacklist())) {
				throw new AssertionError(e);
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
			throw new IllegalStateException("Do not try to interpolate when trace is feasible");
		default:
			throw new AssertionError("unknown case : " + status.getStatus());
		}
		final boolean throwException = category.throwException(mStrategy.getExceptionBlacklist());
		if (throwException) {
			throw new AssertionError(status.getException());
		}
		final String message = status.getException() == null ? "Unknown" : status.getException().getMessage();
		mLogger.info("Interpolation failed due to " + category + ": " + message);
		return null;
	}

	private void logModule(final String msg, final Object module) {
		mLogger.info("%s %s [%s]", msg, module.getClass().getSimpleName(), module.hashCode());
	}
}
