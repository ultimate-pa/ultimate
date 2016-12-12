/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.CachingHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolantConsolidation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerSpWp;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerUtils.InterpolantsPreconditionPostcondition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IRefinementStrategy.RefinementStrategyAdvance;

/**
 * Checks a trace for feasibility and, if infeasible, constructs an interpolant automaton.<br>
 * This class is used in the {@link BasicCegarLoop}.
 * <p>
 * TODO add timeout checks?
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public final class TraceAbstractionRefinementEngine
		implements IRefinementEngine<NestedWordAutomaton<CodeBlock, IPredicate>> {
	
	private final ILogger mLogger;
	private final RefinementStrategyExceptionBlacklist mExceptionBlacklist;
	
	/* outputs */
	private final PredicateUnifier mPredicateUnifier;
	private final LBool mFeasibility;
	private NestedWordAutomaton<CodeBlock, IPredicate> mInterpolantAutomaton;
	private RcfgProgramExecution mRcfgProgramExecution;
	private CachingHoareTripleChecker mHoareTripleChecker;
	
	/**
	 * @param services
	 *            Ultimate services.
	 * @param logger
	 *            logger
	 * @param strategy
	 */
	public TraceAbstractionRefinementEngine(final ILogger logger, final IRefinementStrategy strategy) {
		// initialize fields
		mLogger = logger;
		mExceptionBlacklist = strategy.getExceptionBlacklist();
		mPredicateUnifier = strategy.getPredicateUnifier();
		mLogger.info("Using refinement strategy " + strategy.getClass().getSimpleName());
		mFeasibility = executeStrategy(strategy);
	}
	
	@Override
	public LBool getCounterexampleFeasibility() {
		return mFeasibility;
	}
	
	@Override
	public RcfgProgramExecution getRcfgProgramExecution() {
		return mRcfgProgramExecution;
	}
	
	@Override
	public NestedWordAutomaton<CodeBlock, IPredicate> getInfeasibilityProof() {
		return mInterpolantAutomaton;
	}
	
	@Override
	public PredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}
	
	@Override
	public CachingHoareTripleChecker getHoareTripleChecker() {
		return mHoareTripleChecker;
	}
	
	/**
	 * This method is the heart of the refinement engine.<br>
	 * It first checks feasibility of the counterexample. If infeasible, the method tries to find a perfect interpolant
	 * sequence. If unsuccessful, it collects all tested sequences. In the end an interpolant automaton is created.
	 *
	 * @param strategy
	 *            refinement strategy
	 * @return counterexample feasibility
	 */
	private LBool executeStrategy(final IRefinementStrategy strategy) {
		final List<InterpolantsPreconditionPostcondition> interpolantSequences = new LinkedList<>();
		while (true) {
			/*
			 * check feasibility using the strategy
			 * 
			 * NOTE: Logically, this method should be called outside the loop. However, since the result is cached,
			 * asking the same trace checker several times does not cost much. On the plus side, the strategy does not
			 * have to take care of exception handling if it decides to exchange the backing trace checker.
			 */
			final LBool feasibility = checkFeasibility(strategy);
			
			switch (feasibility) {
			case SAT:
				// feasible counterexample, nothing more to do here
				handleFeasibleOrUnknownCase(strategy);
				return LBool.SAT;
			case UNKNOWN:
				if (!interpolantSequences.isEmpty()) {
					// infeasibility was shown in previous attempt already
					constructAutomatonFromImperfectSequences(strategy, interpolantSequences);
					return LBool.UNSAT;
				}
				if (mLogger.isInfoEnabled()) {
					mLogger.info("Strategy " + strategy.getClass().getSimpleName()
							+ " was unsuccessful and could not determine trace feasibility.");
				}
				handleFeasibleOrUnknownCase(strategy);
				return LBool.UNKNOWN;
			case UNSAT:
				final List<InterpolantsPreconditionPostcondition> perfectInterpolantsList =
						handleInterpolantsCase(strategy, interpolantSequences);
				if (!perfectInterpolantsList.isEmpty()) {
					// construct interpolant automaton using the perfect sequence
					constructAutomatonFromPerfectSequence(strategy, perfectInterpolantsList, feasibility);
					return LBool.UNSAT;
				}
				if (strategy.hasNext(RefinementStrategyAdvance.INTERPOLANT_GENERATOR)) {
					// construct the next sequence of interpolants
					if (mLogger.isInfoEnabled()) {
						mLogger.info("The current sequence of interpolants is not perfect, trying the next one.");
					}
					strategy.next(RefinementStrategyAdvance.INTERPOLANT_GENERATOR);
					continue;
				}
				constructAutomatonFromImperfectSequences(strategy, interpolantSequences);
				return LBool.UNSAT;
			default:
				throw new IllegalArgumentException("Unknown case: " + feasibility);
			}
		}
	}
	
	private LBool checkFeasibility(final IRefinementStrategy strategy) {
		while (true) {
			// NOTE: Do not convert to method reference!
			final Supplier<LBool> tc = () -> strategy.getTraceChecker().isCorrect();
			LBool feasibility = handleExceptions(tc);
			if (feasibility == null) {
				feasibility = LBool.UNKNOWN;
			}
			
			if (feasibility == LBool.UNKNOWN && strategy.hasNext(RefinementStrategyAdvance.TRACE_CHECKER)) {
				// feasibility check failed, try next combination in the strategy
				mLogger.info("Advancing trace checker");
				strategy.next(RefinementStrategyAdvance.TRACE_CHECKER);
			} else {
				return feasibility;
			}
		}
	}
	
	private void handleFeasibleOrUnknownCase(final IRefinementStrategy strategy) {
		// NOTE: This can crash, but such a crash is intended.
		mRcfgProgramExecution = strategy.getTraceChecker().getRcfgProgramExecution();
	}
	
	/**
	 * There is a huge hack for supporting the special {@link TraceCheckerSpWp} architecture because
	 * <ol>
	 * <li>we need a different getter for the interpolant sequence and</li>
	 * <li>there are two sequences of interpolants.</li>
	 * </ol>
	 * 
	 * @return perfect interpolant sequence or {@code null}
	 */
	private List<InterpolantsPreconditionPostcondition> handleInterpolantsCase(final IRefinementStrategy strategy,
			final List<InterpolantsPreconditionPostcondition> interpolantSequences) {
		final IInterpolantGenerator interpolantGenerator = handleExceptions(strategy::getInterpolantGenerator);
		if (interpolantGenerator == null) {
			return Collections.emptyList();
		}
		
		if (interpolantGenerator instanceof InterpolantConsolidation) {
			// set Hoare triple checker
			mHoareTripleChecker = ((InterpolantConsolidation) interpolantGenerator).getHoareTripleChecker();
		}
		
		if (interpolantGenerator instanceof TraceCheckerSpWp) {
			return handleTraceCheckerSpWpCase(interpolantSequences, (TraceCheckerSpWp) interpolantGenerator);
		}
		
		final InterpolantsPreconditionPostcondition interpolants = interpolantGenerator.getIpp();
		final boolean perfectInterpolantsFound = strategy.getInterpolantGenerator().isPerfectSequence();
		if (perfectInterpolantsFound) {
			return Collections.singletonList(interpolants);
		}
		if (interpolantGenerator.imperfectSequencesUsable()) {
			interpolantSequences.add(interpolants);
		}
		return Collections.emptyList();
	}
	
	/**
	 * NOTE: This method is complicated due to the structure of the {@link TraceCheckerSpWp}.
	 */
	private static List<InterpolantsPreconditionPostcondition> handleTraceCheckerSpWpCase(
			final List<InterpolantsPreconditionPostcondition> interpolantSequences,
			final TraceCheckerSpWp traceCheckerSpWp) {
		final List<InterpolantsPreconditionPostcondition> interpolantsList = new ArrayList<>(2);
		boolean oneSequenceWasPerfect;
		if (traceCheckerSpWp.forwardsPredicatesComputed()) {
			oneSequenceWasPerfect = addForwardPredicates(traceCheckerSpWp, interpolantsList);
			if (traceCheckerSpWp.backwardsPredicatesComputed()) {
				oneSequenceWasPerfect = addBackwardPredicates(traceCheckerSpWp, interpolantsList);
			}
		} else if (traceCheckerSpWp.backwardsPredicatesComputed()) {
			oneSequenceWasPerfect = addBackwardPredicates(traceCheckerSpWp, interpolantsList);
		} else {
			return Collections.emptyList();
		}
		
		if (oneSequenceWasPerfect) {
			return interpolantsList;
		}
		interpolantSequences.addAll(interpolantsList);
		return Collections.emptyList();
	}
	
	private static boolean addForwardPredicates(final TraceCheckerSpWp traceCheckerSpWp,
			final List<InterpolantsPreconditionPostcondition> interpolantsList) {
		final InterpolantsPreconditionPostcondition interpolants = traceCheckerSpWp.getForwardIpp();
		assert interpolants != null;
		interpolantsList.add(interpolants);
		return traceCheckerSpWp.isPerfectSequence(true);
	}
	
	private static boolean addBackwardPredicates(final TraceCheckerSpWp traceCheckerSpWp,
			final List<InterpolantsPreconditionPostcondition> interpolantsList) {
		final InterpolantsPreconditionPostcondition interpolants = traceCheckerSpWp.getBackwardIpp();
		assert interpolants != null;
		interpolantsList.add(interpolants);
		return traceCheckerSpWp.isPerfectSequence(false);
	}
	
	private LBool constructAutomatonFromPerfectSequence(final IRefinementStrategy strategy,
			final List<InterpolantsPreconditionPostcondition> interpolantsList, final LBool feasibility) {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Found a perfect sequence of interpolants.");
		}
		mInterpolantAutomaton = strategy.getInterpolantAutomatonBuilder(interpolantsList).getResult();
		return feasibility;
	}
	
	private void constructAutomatonFromImperfectSequences(final IRefinementStrategy strategy,
			final List<InterpolantsPreconditionPostcondition> interpolantSequences) {
		// construct the interpolant automaton from the sequences we have found previously
		if (mLogger.isInfoEnabled()) {
			mLogger.info("No perfect sequence of interpolants found, combining those we have.");
		}
		mInterpolantAutomaton = strategy.getInterpolantAutomatonBuilder(interpolantSequences).getResult();
	}
	
	/**
	 * Wraps the exception handling during {@link TraceChecker} or {@link IInterpolantGenerator} construction.
	 */
	@SuppressWarnings("squid:S1871")
	private <T> T handleExceptions(final Supplier<T> supp) {
		Exception exception;
		ExceptionHandlingCategory exceptionCategory;
		try {
			return supp.get();
		} catch (final UnsupportedOperationException e) {
			exception = e;
			final String message = e.getMessage();
			if (message == null) {
				exceptionCategory = ExceptionHandlingCategory.UNKNOWN;
			} else if (message.startsWith("Cannot interpolate")) {
				// SMTInterpol throws this during interpolation for unsupported fragments such as arrays
				exceptionCategory = ExceptionHandlingCategory.KNOWN_IGNORE;
			} else {
				exceptionCategory = ExceptionHandlingCategory.UNKNOWN;
			}
		} catch (final SMTLIBException e) {
			exception = e;
			final String message = e.getMessage();
			if (message == null) {
				exceptionCategory = ExceptionHandlingCategory.UNKNOWN;
			} else if ("Unsupported non-linear arithmetic".equals(message)) {
				// SMTInterpol does not support non-linear arithmetic
				exceptionCategory = ExceptionHandlingCategory.KNOWN_IGNORE;
			} else if (message.endsWith("Connection to SMT solver broken")) {
				// broken SMT solver connection can have various reasons such as misconfiguration or solver crashes
				exceptionCategory = ExceptionHandlingCategory.KNOWN_DEPENDING;
			} else if (message.endsWith("Received EOF on stdin. No stderr output.")) {
				// problem with Z3
				exceptionCategory = ExceptionHandlingCategory.KNOWN_IGNORE;
			} else if (message.contains("Received EOF on stdin. stderr output:")) {
				// problem with CVC4
				exceptionCategory = ExceptionHandlingCategory.KNOWN_THROW;
			} else if (message.startsWith("Logic does not allow numerals")) {
				// wrong usage of external solver, tell the user
				exceptionCategory = ExceptionHandlingCategory.KNOWN_THROW;
			} else {
				exceptionCategory = ExceptionHandlingCategory.UNKNOWN;
			}
		}
		
		switch (exceptionCategory) {
		case KNOWN_IGNORE:
		case KNOWN_DEPENDING:
		case KNOWN_THROW:
			if (mLogger.isErrorEnabled()) {
				mLogger.error("Caught known exception: " + exception.getMessage());
			}
			break;
		case UNKNOWN:
			if (mLogger.isErrorEnabled()) {
				mLogger.error("Caught unknown exception: " + exception.getMessage());
			}
			break;
		default:
			throw new IllegalArgumentException("Unknown exception category: " + exceptionCategory);
		}
		
		final boolean throwException = exceptionCategory.throwException(mExceptionBlacklist);
		if (throwException) {
			if (mLogger.isInfoEnabled()) {
				mLogger.info("Global settings require throwing the exception.");
			}
			throw new AssertionError(exception);
		}
		
		return null;
	}
	
	/**
	 * Categories for exception handling.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public enum ExceptionHandlingCategory {
		/**
		 * The exception is known and we always want to ignore it.
		 */
		KNOWN_IGNORE,
		/**
		 * The exception is known and we sometimes want it to be thrown depending on the use case.
		 */
		KNOWN_DEPENDING,
		/**
		 * The exception is known and we always want it to be thrown.
		 */
		KNOWN_THROW,
		/**
		 * The exception is unknown and we usually want it to be thrown.
		 */
		UNKNOWN;
		
		/**
		 * @param throwSpecification
		 *            Specifies which exception categories should be thrown.
		 * @return {@code true} iff this exception category should be thrown.
		 */
		public boolean throwException(final RefinementStrategyExceptionBlacklist throwSpecification) {
			switch (throwSpecification) {
			case ALL:
				return true;
			case UNKNOWN:
				return this == UNKNOWN || this == KNOWN_THROW;
			case DEPENDING:
				return this == UNKNOWN || this == KNOWN_THROW || this == KNOWN_DEPENDING;
			case NONE:
				return false;
			default:
				throw new IllegalArgumentException("Unknown category specification: " + throwSpecification);
			}
		}
	}
}
