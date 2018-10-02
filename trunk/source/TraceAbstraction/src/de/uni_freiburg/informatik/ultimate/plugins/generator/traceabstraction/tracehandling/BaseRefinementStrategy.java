/*
 * Copyright (C) 2016-2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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
import java.util.LinkedList;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.ITraceCheck;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.ExceptionHandlingCategory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbsIntBaseInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.IInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.InterpolantAutomatonBuilderFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.CachingHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolantConsolidation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolantConsolidation.InterpolantConsolidationBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckSpWp;

/**
 * A {@link BaseRefinementStrategy} allows an {@link IRefinementEngine} to try multiple combinations of
 * <ol>
 * <li>a {@link TraceCheck},</li>
 * <li>an {@link IInterpolantGenerator}, and</li>
 * <li>an {@link InterpolantAutomatonBuilderFactory}.</li>
 * </ol>
 * In the following class documentation this combination is just called "combination".
 * <p>
 * The contract is that if {@link #hasNextTraceCheck()} (resp. {@link #hasNextInterpolantGenerator(List, List)}) returns
 * {@code true}, then {@link #nextTraceCheck()} (resp. {@link #nextInterpolantGenerator()}) advances the respective
 * component (but the strategy may also return {@code false} to enforce early termination).<br>
 * Between two calls to {@link #nextTraceCheck()} (resp. {@link #nextInterpolantGenerator()}) the respective getter (
 * {@link #getTraceCheck()} resp. {@link IRefinementStrategy#getInterpolantGenerator()}) always returns the same object
 * and {@link #hasNextTraceCheck()} (resp. {@link #hasNextInterpolantGenerator(List, List)}) always returns the same
 * answer. However, for instance by a call to {@link #nextInterpolantGenerator()}, the {@link TraceCheck} may change. A
 * user should hence not store these objects temporarily.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 */
public abstract class BaseRefinementStrategy<LETTER extends IIcfgTransition<?>> {

	private final ILogger mLogger;

	/* outputs */
	private NestedWordAutomaton<LETTER, IPredicate> mInterpolantAutomaton;
	private boolean mProvidesIcfgProgramExecution;
	private IProgramExecution<IIcfgTransition<IcfgLocation>, Term> mIcfgProgramExecution;
	private CachingHoareTripleChecker mHoareTripleChecker;
	private boolean mSomePerfectSequenceFound = false;
	protected final IEmptyStackStateFactory<IPredicate> mEmptyStackFactory;

	private InterpolantConsolidationBenchmarkGenerator mInterpolantConsolidationStatistics;

	public BaseRefinementStrategy(final ILogger logger, final IEmptyStackStateFactory<IPredicate> emptyStackFactory) {
		mLogger = logger;
		mEmptyStackFactory = emptyStackFactory;
	}

	/**
	 * A user should use this method whenever the trace check was unsuccessful (i.e., crashed or returned
	 * {@link LBool.UNKNOWN}. The strategy then decides whether it wants to and whether it can use another
	 * {@link TraceCheck}.
	 *
	 * @return {@code true} iff there is another {@link TraceCheck} available and should be used
	 */
	public abstract boolean hasNextTraceCheck();

	/**
	 * Changes the {@link TraceCheck}.<br>
	 * Throws a {@link NoSuchElementException} if there is no next {@link TraceCheck}; use {@link #hasNextTraceCheck()}
	 * to check this.
	 */
	public abstract void nextTraceCheck();

	/**
	 * @return The trace checker of the current combination.
	 */
	public abstract ITraceCheck getTraceCheck();

	/**
	 * A user should use this method whenever new interpolants have been computed (or the computation has failed). The
	 * strategy then decides whether it wants to and whether it can use another {@link IInterpolantGenerator}.
	 *
	 * @param perfectIpps
	 *            perfect interpolant sequences constructed so far
	 * @param imperfectIpps
	 *            imperfect interpolant sequences constructed so far
	 * @return {@code true} iff there is another {@link IInterpolantGenerator} available and should be used
	 */
	public abstract boolean hasNextInterpolantGenerator(List<TracePredicates> perfectIpps,
			List<TracePredicates> imperfectIpps);

	/**
	 * Changes the {@link IInterpolantGenerator}.<br>
	 * Throws a {@link NoSuchElementException} if there is no next {@link IInterpolantGenerator}; use
	 * {@link #hasNextInterpolantGenerator(List, List)} to check this.
	 */
	public abstract void nextInterpolantGenerator();

	/**
	 * This method must only be called if the {@link TraceCheck} returns {@code UNSAT}.
	 *
	 * @return The interpolant generator of the current combination.
	 */
	public abstract IInterpolantGenerator<LETTER> getInterpolantGenerator();

	/**
	 * @param perfectIpps
	 *            Sequences of perfect interpolants.
	 * @param imperfectIpps
	 *            sequences of imperfect interpolants
	 * @return an interpolant automaton builder
	 */
	public abstract IInterpolantAutomatonBuilder<LETTER, IPredicate>
			getInterpolantAutomatonBuilder(List<TracePredicates> perfectIpps, List<TracePredicates> imperfectIpps);

	/**
	 * @return Predicate unifier.
	 */
	public abstract IPredicateUnifier getPredicateUnifier();

	/**
	 * @return Object that encapsulates which exceptions are blacklisted.
	 * @see RefinementStrategyExceptionBlacklist
	 */
	public abstract RefinementStrategyExceptionBlacklist getExceptionBlacklist();

	public abstract RefinementEngineStatisticsGenerator getRefinementEngineStatistics();

	/**
	 * This method is the heart of the refinement engine.<br>
	 * It first checks feasibility of the counterexample. If infeasible, the method tries to find a perfect interpolant
	 * sequence. If unsuccessful, it collects all tested sequences. In the end an interpolant automaton is created.
	 *
	 * @return counterexample feasibility
	 */
	public LBool executeStrategy() {
		final List<TracePredicates> perfectIpps = new LinkedList<>();
		final List<TracePredicates> imperfectIpps = new LinkedList<>();
		while (true) {
			/*
			 * check feasibility using the strategy
			 *
			 * NOTE: Logically, this method should be called outside the loop. However, since the result is cached,
			 * asking the same trace checker several times does not cost much. On the plus side, the strategy does not
			 * have to take care of exception handling if it decides to exchange the backing trace checker.
			 */
			final LBool feasibility = checkFeasibility();

			switch (feasibility) {
			case SAT:
				// feasible counterexample, nothing more to do here
				return handleFeasibleCase();
			case UNKNOWN:
				return handleUnknownCase(perfectIpps, imperfectIpps);
			case UNSAT:
				final boolean doContinue = handleInfeasibleCase(perfectIpps, imperfectIpps);
				if (!perfectIpps.isEmpty()) {
					mSomePerfectSequenceFound = true;
				}
				if (doContinue) {
					continue;
				}
				return constructAutomatonFromIpps(perfectIpps, imperfectIpps);
			default:
				throw new IllegalArgumentException("Unknown case: " + feasibility);
			}
		}
	}

	private LBool checkFeasibility() {
		while (true) {
			// NOTE: Do not convert to method reference!
			final LBool feasibility = getTraceCheck().isCorrect();
			Objects.requireNonNull(feasibility);

			if (feasibility == LBool.UNKNOWN) {
				final TraceCheckReasonUnknown tcra = getTraceCheck().getTraceCheckReasonUnknown();
				if (tcra.getException() != null) {
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
							tcra.getExceptionHandlingCategory().throwException(getExceptionBlacklist());
					if (throwException) {
						if (mLogger.isInfoEnabled()) {
							mLogger.info("Global settings require throwing the exception.");
						}
						throw new AssertionError(tcra.getException());
					}
				}

				if (hasNextTraceCheck()) {
					// feasibility check failed, try next combination in the strategy
					mLogger.info("Advancing trace checker");
					nextTraceCheck();
				} else {
					return feasibility;
				}
			} else {
				return feasibility;
			}
		}
	}

	private LBool handleFeasibleCase() {
		if (getTraceCheck().providesRcfgProgramExecution()) {
			mProvidesIcfgProgramExecution = true;
			mIcfgProgramExecution = getTraceCheck().getRcfgProgramExecution();
		}
		return LBool.SAT;
	}

	private LBool handleUnknownCase(final List<TracePredicates> perfectIpps,
			final List<TracePredicates> imperfectIpps) {
		if (perfectIpps.size() + imperfectIpps.size() > 0) {
			// infeasibility was shown in previous attempt already
			constructAutomatonFromIpps(perfectIpps, imperfectIpps);
			return LBool.UNSAT;
		}
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Strategy " + getClass().getSimpleName()
					+ " was unsuccessful and could not determine trace feasibility.");
		}
		return LBool.UNKNOWN;
	}

	/**
	 * @return {@code true} iff outer loop should be continued.
	 */
	private boolean handleInfeasibleCase(final List<TracePredicates> perfectIpps,
			final List<TracePredicates> imperfectIpps) {
		extractInterpolants(perfectIpps, imperfectIpps);
		if (hasNextInterpolantGenerator(perfectIpps, imperfectIpps)) {
			// construct the next sequence of interpolants
			if (mLogger.isInfoEnabled()) {
				mLogger.info("The current sequences of interpolants are not accepted, trying to find more.");
			}
			nextInterpolantGenerator();
			return true;
		}
		return false;
	}

	protected LBool constructAutomatonFromIpps(final List<TracePredicates> perfectIpps,
			final List<TracePredicates> imperfectIpps) {
		// construct the interpolant automaton from the sequences we have found
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Constructing automaton from " + perfectIpps.size() + " perfect and " + imperfectIpps.size()
					+ " imperfect interpolant sequences.");
		}
		if (mLogger.isInfoEnabled()) {
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
		mInterpolantAutomaton = getInterpolantAutomatonBuilder(perfectIpps, imperfectIpps).getResult();
		if (!perfectIpps.isEmpty()) {
			mSomePerfectSequenceFound = true;
		}
		return LBool.UNSAT;
	}

	/**
	 * NOTE: This method is complicated due to the structure of the {@link TraceCheckSpWp} because
	 * <ol>
	 * <li>we need a different getter for the interpolant sequence and</li>
	 * <li>there are two sequences of interpolants.</li>
	 * </ol>
	 */
	private void handleTraceCheckSpWpCase(final List<TracePredicates> perfectIpps,
			final List<TracePredicates> imperfectIpps, final TraceCheckSpWp<LETTER> traceCheckSpWp) {
		if (traceCheckSpWp.wasForwardPredicateComputationRequested()) {
			addForwardPredicates(traceCheckSpWp, perfectIpps, imperfectIpps);
		}
		if (traceCheckSpWp.wasBackwardSequenceConstructed()) {
			addBackwardPredicates(traceCheckSpWp, perfectIpps, imperfectIpps);
		}
	}

	private void addForwardPredicates(final TraceCheckSpWp<LETTER> traceCheckSpWp,
			final List<TracePredicates> perfectIpps, final List<TracePredicates> imperfectIpps) {
		final TracePredicates interpolants = traceCheckSpWp.getForwardIpp();
		assert interpolants != null;
		if (traceCheckSpWp.isForwardSequencePerfect()) {
			perfectIpps.add(interpolants);
		} else {
			imperfectIpps.add(interpolants);
		}
	}

	private void addBackwardPredicates(final TraceCheckSpWp<LETTER> traceCheckSpWp,
			final List<TracePredicates> perfectIpps, final List<TracePredicates> imperfectIpps) {
		final TracePredicates interpolants = traceCheckSpWp.getBackwardIpp();
		assert interpolants != null;
		if (traceCheckSpWp.isBackwardSequencePerfect()) {
			perfectIpps.add(interpolants);
		} else {
			imperfectIpps.add(interpolants);
		}
	}

	private void extractInterpolants(final List<TracePredicates> perfectIpps,
			final List<TracePredicates> imperfectIpps) {
		IInterpolantGenerator<LETTER> interpolantGenerator = null;
		try {
			interpolantGenerator = getInterpolantGenerator();
			if (interpolantGenerator instanceof InterpolantConsolidation) {
				mInterpolantConsolidationStatistics = ((InterpolantConsolidation<LETTER>) interpolantGenerator)
						.getInterpolantConsolidationBenchmarks();
			}
		} catch (final ToolchainCanceledException tce) {
			throw tce;
		} catch (final Exception e) {
			final ExceptionHandlingCategory category = ExceptionHandlingCategory.UNKNOWN;
			final boolean throwException = category.throwException(getExceptionBlacklist());
			if (throwException) {
				throw new AssertionError(e);
			}
			mLogger.fatal("Ignoring exception!", e);
			return;
		}
		final InterpolantComputationStatus status = interpolantGenerator.getInterpolantComputationStatus();
		if (!status.wasComputationSuccesful()) {
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
				throw new IllegalStateException("should not try to interpolate");
			default:
				throw new AssertionError("unknown case : " + status.getStatus());
			}
			final boolean throwException = category.throwException(getExceptionBlacklist());
			if (throwException) {
				throw new AssertionError(status.getException());
			}
			final String message = status.getException() == null ? "Unknown" : status.getException().getMessage();
			mLogger.info("Interpolation failed due to " + category + ": " + message);
			return;
		}

		if (interpolantGenerator instanceof InterpolantConsolidation<?>) {
			// set Hoare triple checker
			mHoareTripleChecker = ((InterpolantConsolidation<?>) interpolantGenerator).getHoareTripleChecker();
		} else if (interpolantGenerator instanceof AbsIntBaseInterpolantGenerator) {
			mHoareTripleChecker =
					((AbsIntBaseInterpolantGenerator<LETTER>) interpolantGenerator).getHoareTripleChecker();
		}

		if (interpolantGenerator instanceof TraceCheckSpWp) {
			handleTraceCheckSpWpCase(perfectIpps, imperfectIpps, (TraceCheckSpWp<LETTER>) interpolantGenerator);
			return;
		}

		final TracePredicates interpolants = interpolantGenerator.getIpp();
		final boolean interpolantsArePerfect = interpolantGenerator.isPerfectSequence();
		if (interpolantsArePerfect) {
			perfectIpps.add(interpolants);
		} else if (interpolantGenerator.imperfectSequencesUsable()) {
			imperfectIpps.add(interpolants);
		}
	}

	protected InterpolantConsolidationBenchmarkGenerator getInterpolantConsolidationStatistics() {
		return mInterpolantConsolidationStatistics;
	}

	protected NestedWordAutomaton<LETTER, IPredicate> getInfeasibilityProof() {
		return mInterpolantAutomaton;
	}

	protected boolean providesICfgProgramExecution() {
		return mProvidesIcfgProgramExecution;
	}

	protected IProgramExecution<IIcfgTransition<IcfgLocation>, Term> getIcfgProgramExecution() {
		return mIcfgProgramExecution;
	}

	protected CachingHoareTripleChecker getHoareTripleChecker() {
		return mHoareTripleChecker;
	}

	protected boolean somePerfectSequenceFound() {
		return mSomePerfectSequenceFound;
	}
}
