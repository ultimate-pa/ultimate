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

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.CachingHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
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
	 * @param prefs
	 *            preferences
	 * @param predicateFactory
	 *            predicate factory
	 * @param icfgContainer
	 *            ICFG container
	 * @param simplificationTechnique
	 *            simplification technique
	 * @param xnfConversionTechnique
	 *            XNF conversion technique
	 * @param toolchainStorage
	 *            toolchain storage
	 * @param taPrefsForInterpolantConsolidation
	 *            trace abstraction preferences (only used for interpolant consolidation)
	 * @param iteration
	 *            current iteration
	 * @param counterexample
	 *            counterexample
	 * @param abstraction
	 *            old abstraction
	 */
	public TraceAbstractionRefinementEngine(final IUltimateServiceProvider services, final ILogger logger,
			final TaCheckAndRefinementPreferences prefs, final PredicateFactory predicateFactory,
			final BoogieIcfgContainer icfgContainer, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final IToolchainStorage toolchainStorage,
			final TAPreferences taPrefsForInterpolantConsolidation, final int iteration,
			final IRun<CodeBlock, IPredicate, ?> counterexample, final IAutomaton<CodeBlock, IPredicate> abstraction) {
		// initialize fields
		mLogger = logger;
		mExceptionBlacklist = prefs.getExceptionBlacklist();
		
		mPredicateUnifier = new PredicateUnifier(services, prefs.getCfgSmtToolkit().getManagedScript(),
				predicateFactory, icfgContainer.getBoogie2SMT().getBoogie2SmtSymbolTable(), simplificationTechnique,
				xnfConversionTechnique);
		
		final ManagedScript managedScript =
				setupManagedScriptInternal(services, prefs, icfgContainer, toolchainStorage, iteration);
		
		final IRefinementStrategy strategy = chooseStrategy(counterexample, abstraction, services, managedScript,
				taPrefsForInterpolantConsolidation, prefs);
		
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
	
	private IRefinementStrategy chooseStrategy(final IRun<CodeBlock, IPredicate, ?> counterexample,
			final IAutomaton<CodeBlock, IPredicate> abstraction, final IUltimateServiceProvider services,
			final ManagedScript managedScript, final TAPreferences taPrefsForInterpolantConsolidation,
			final TaCheckAndRefinementPreferences prefs) {
		switch (prefs.getRefinementStrategy()) {
			case FIXED_PREFERENCES:
				return new FixedTraceAbstractionRefinementStrategy(mLogger, prefs, managedScript, services,
						mPredicateUnifier, counterexample, abstraction, taPrefsForInterpolantConsolidation);
			case MULTI_TRACK:
				return new MultiTrackTraceAbstractionRefinementStrategy(mLogger, prefs, services, mPredicateUnifier,
						counterexample, abstraction, taPrefsForInterpolantConsolidation);
			case TAIPAN:
				return new TaipanRefinementStrategy(mLogger, services, prefs, mPredicateUnifier, counterexample,
						abstraction);
			default:
				throw new IllegalArgumentException(
						"Unknown refinement strategy specified: " + prefs.getRefinementStrategy());
		}
	}
	
	/**
	 * This method is the heart of the refinement engine.<br>
	 * It first checks feasibility of the counterexample. If infeasible, the method tries to find a perfect interpolant
	 * sequence. If unsuccessful, it collects all tested sequences. In the end an interpolant automaton is created.
	 * <p>
	 * There is a huge hack for supporting the special {@link TraceCheckerSpWp} architecture because
	 * <ol>
	 * <li>we need a different getter for the interpolant sequence and</li>
	 * <li>there are two sequences of interpolants.</li>
	 * </ol>
	 * 
	 * @param strategy
	 *            refinement strategy
	 * @return counterexample feasibility
	 */
	@SuppressWarnings("squid:LabelsShouldNotBeUsedCheck")
	private LBool executeStrategy(final IRefinementStrategy strategy) {
		List<InterpolantsPreconditionPostcondition> interpolantSequences = new LinkedList<>();
		boolean perfectInterpolantsFound = false;
		outer: do {
			// check feasibility using the strategy
			LBool feasibility = wrapExceptionHandling(() -> strategy.getTraceChecker().isCorrect());
			if (feasibility == null) {
				feasibility = LBool.UNKNOWN;
			}
			
			if (feasibility == LBool.UNKNOWN && strategy.hasNext(RefinementStrategyAdvance.TRACE_CHECKER)) {
				// feasibility check failed, try next combination in the strategy
				strategy.next(RefinementStrategyAdvance.TRACE_CHECKER);
				continue outer;
			}
			
			switch (feasibility) {
				case UNKNOWN:
					if (!interpolantSequences.isEmpty()) {
						// construct the interpolant automaton from the sequences we have found previously
						if (mLogger.isInfoEnabled()) {
							mLogger.info("No perfect sequence of interpolants found, combining those we have.");
						}
						feasibility = LBool.UNSAT;
						mInterpolantAutomaton =
								strategy.getInterpolantAutomatonBuilder(interpolantSequences).getResult();
					} else {
						if (mLogger.isInfoEnabled()) {
							mLogger.info("Strategy " + strategy.getClass().getSimpleName()
									+ " was unsuccessful and could not determine trace feasibility.");
						}
						// NOTE: This can crash as well, but such a crash is intended.
						mRcfgProgramExecution = strategy.getTraceChecker().getRcfgProgramExecution();
					}
					break;
				case UNSAT:
					final IInterpolantGenerator interpolantGenerator =
							wrapExceptionHandling(() -> strategy.getInterpolantGenerator());
					
					if (interpolantGenerator != null) {
						if (interpolantGenerator instanceof InterpolantConsolidation) {
							// set Hoare triple checker
							mHoareTripleChecker =
									((InterpolantConsolidation) interpolantGenerator).getHoareTripleChecker();
						}
						
						InterpolantsPreconditionPostcondition interpolants;
						int numberOfInterpolantSequencesAvailable;
						if (interpolantGenerator instanceof TraceCheckerSpWp) {
							final TraceCheckerSpWp traceCheckerSpWp = (TraceCheckerSpWp) interpolantGenerator;
							numberOfInterpolantSequencesAvailable = 0;
							if (traceCheckerSpWp.forwardsPredicatesComputed()) {
								interpolants = traceCheckerSpWp.getForwardIpp();
								++numberOfInterpolantSequencesAvailable;
								if (traceCheckerSpWp.backwardsPredicatesComputed()) {
									++numberOfInterpolantSequencesAvailable;
								}
							} else {
								interpolants = traceCheckerSpWp.backwardsPredicatesComputed()
										? traceCheckerSpWp.getBackwardIpp()
										: null;
								numberOfInterpolantSequencesAvailable = 1;
							}
						} else {
							interpolants = interpolantGenerator.getIpp();
							numberOfInterpolantSequencesAvailable = 1;
						}
						
						for (int i = 1; i <= numberOfInterpolantSequencesAvailable; ++i) {
							if (i == 2) {
								interpolants = ((TraceCheckerSpWp) interpolantGenerator).getBackwardIpp();
							}
							if (interpolants == null) {
								continue;
							}
							if (interpolantGenerator instanceof TraceCheckerSpWp) {
								perfectInterpolantsFound =
										((TraceCheckerSpWp) interpolantGenerator).isPerfectSequence(i == 1);
							} else {
								perfectInterpolantsFound = strategy.getInterpolantGenerator().isPerfectSequence();
							}
							if (perfectInterpolantsFound) {
								// construct interpolant automaton using only this (perfect) sequence
								interpolantSequences = Collections.singletonList(interpolants);
								if (mLogger.isInfoEnabled()) {
									mLogger.info("Found a perfect sequence of interpolants.");
								}
								break;
							}
							interpolantSequences.add(interpolants);
						}
					}
					if (!perfectInterpolantsFound) {
						if (strategy.hasNext(RefinementStrategyAdvance.INTERPOLANT_GENERATOR)) {
							// construct the next sequence of interpolants
							if (mLogger.isInfoEnabled()) {
								mLogger.info(
										"The current sequence of interpolants is not perfect, trying the next one.");
							}
							strategy.next(RefinementStrategyAdvance.INTERPOLANT_GENERATOR);
							continue outer;
						} else if (mLogger.isInfoEnabled()) {
							mLogger.info("No perfect sequence of interpolants found, combining those we have.");
						}
					}
					
					// construct the interpolant automaton from the sequences
					mInterpolantAutomaton = strategy.getInterpolantAutomatonBuilder(interpolantSequences).getResult();
					break;
				case SAT:
					// feasible counterexample, nothing more to do here
					mRcfgProgramExecution = strategy.getTraceChecker().getRcfgProgramExecution();
					break;
				default:
					throw new IllegalArgumentException("Unknown case: " + feasibility);
			}
			
			return feasibility;
		} while (true);
	}
	
	/**
	 * Wraps the exception handling during {@link TraceChecker} or {@link IInterpolantGenerator} construction.
	 */
	private <T> T wrapExceptionHandling(final Supplier<T> supp) {
		Exception exception = null;
		ExceptionHandlingCategory exceptionCategory = ExceptionHandlingCategory.UNKNOWN;
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
				// SMT solver does not support non-linear arithmetic
				exceptionCategory = ExceptionHandlingCategory.KNOWN_IGNORE;
			} else if (message.endsWith("Connection to SMT solver broken")) {
				// broken SMT solver connection can have various reasons such as misconfiguration or solver crashes
				exceptionCategory = ExceptionHandlingCategory.KNOWN_DEPENDING;
			} else if (message.endsWith("Received EOF on stdin. No stderr output.")) {
				// wrong usage of external solver, tell the user
				exceptionCategory = ExceptionHandlingCategory.KNOWN_THROW;
			} else if (message.contains("Received EOF on stdin. stderr output:")) {
				// wrong usage of external solver, tell the user
				exceptionCategory = ExceptionHandlingCategory.KNOWN_THROW;
			} else {
				exceptionCategory = ExceptionHandlingCategory.UNKNOWN;
			}
		}
		
		final boolean throwException = exceptionCategory.throwException(mExceptionBlacklist);
		
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
		
		if (throwException) {
			if (mLogger.isInfoEnabled()) {
				mLogger.info("Global settings require throwing the exception.");
			}
			throw new AssertionError(exception);
		}
		
		return null;
	}
	
	private static ManagedScript setupManagedScriptInternal(final IUltimateServiceProvider services,
			final TaCheckAndRefinementPreferences prefs, final BoogieIcfgContainer icfgContainer,
			final IToolchainStorage toolchainStorage, final int iteration) throws AssertionError {
		final ManagedScript managedScript;
		
		switch (prefs.getRefinementStrategy()) {
			case MULTI_TRACK:
			case TAIPAN:
				managedScript = null;
				break;
			case FIXED_PREFERENCES:
				managedScript = setupManagedScript(services, icfgContainer, toolchainStorage, iteration, prefs);
				break;
			default:
				throw new IllegalArgumentException("Unknown mode: " + prefs.getRefinementStrategy());
		}
		return managedScript;
	}
	
	public static ManagedScript setupManagedScript(final IUltimateServiceProvider services,
			final BoogieIcfgContainer icfgContainer, final IToolchainStorage toolchainStorage, final int iteration,
			final TaCheckAndRefinementPreferences prefs)
			throws AssertionError {
		final ManagedScript mgdScriptTc;
		if (prefs.getUseSeparateSolverForTracechecks()) {
			final String filename = icfgContainer.getFilename() + "_TraceCheck_Iteration" + iteration;
			final SolverMode solverMode = prefs.getSolverMode();
			final boolean fakeNonIncrementalSolver = prefs.getFakeNonIncrementalSolver();
			final String commandExternalSolver = prefs.getCommandExternalSolver();
			final boolean dumpSmtScriptToFile = prefs.getDumpSmtScriptToFile();
			final String pathOfDumpedScript = prefs.getPathOfDumpedScript();
			final Settings solverSettings = SolverBuilder.constructSolverSettings(filename, solverMode,
					fakeNonIncrementalSolver, commandExternalSolver, dumpSmtScriptToFile, pathOfDumpedScript);
			final Script tcSolver = SolverBuilder.buildAndInitializeSolver(services, toolchainStorage,
					prefs.getSolverMode(), solverSettings, false, false, prefs.getLogicForExternalSolver(),
					"TraceCheck_Iteration" + iteration);
			mgdScriptTc = new ManagedScript(services, tcSolver);
			final TermTransferrer tt = new TermTransferrer(tcSolver);
			for (final Term axiom : icfgContainer.getBoogie2SMT().getAxioms()) {
				tcSolver.assertTerm(tt.transform(axiom));
			}
		} else {
			mgdScriptTc = prefs.getCfgSmtToolkit().getManagedScript();
		}
		return mgdScriptTc;
	}
}
