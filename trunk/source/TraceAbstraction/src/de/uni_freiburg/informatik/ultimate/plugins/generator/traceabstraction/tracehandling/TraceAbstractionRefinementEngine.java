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

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolantConsolidation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
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
	
	/* outputs */
	private final PredicateUnifier mPredicateUnifier;
	private final LBool mFeasibility;
	private NestedWordAutomaton<CodeBlock, IPredicate> mInterpolantAutomaton;
	private RcfgProgramExecution mRcfgProgramExecution;
	private final CachingHoareTripleChecker mHoareTripleChecker;
	
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
		
		mPredicateUnifier = new PredicateUnifier(services, prefs.getCfgSmtToolkit().getManagedScript(),
				predicateFactory, icfgContainer.getBoogie2SMT().getBoogie2SmtSymbolTable(), simplificationTechnique,
				xnfConversionTechnique);
		
		final ManagedScript managedScript =
				setupManagedScriptInternal(services, prefs, icfgContainer, toolchainStorage, iteration);
		
		// choose strategy
		final IRefinementStrategy strategy = chooseStrategy(counterexample, abstraction, services, managedScript,
				taPrefsForInterpolantConsolidation, prefs);
		
		mFeasibility = executeStrategy(strategy);
		if (strategy.getInterpolantGenerator() instanceof InterpolantConsolidation) {
			mHoareTripleChecker =
					((InterpolantConsolidation) strategy.getInterpolantGenerator()).getHoareTripleChecker();
		} else {
			mHoareTripleChecker = null;
		}
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
	 * There is a huge hack for supporting the special {@link TraceCheckerSpWp} architecture where
	 * <ol>
	 * <li>we need a different getter for the interpolant sequence and</li>
	 * <li>there are two sequences of interpolants</li>
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
			final LBool feasibility = strategy.getTraceChecker().isCorrect();
			
			if (feasibility == LBool.UNKNOWN && strategy.hasNext(RefinementStrategyAdvance.TRACE_CHECKER)) {
				// feasibility check failed, try next combination in the strategy
				strategy.next(RefinementStrategyAdvance.TRACE_CHECKER);
				continue outer;
			}
			
			switch (feasibility) {
				case UNKNOWN:
					if (mLogger.isInfoEnabled()) {
						mLogger.info("Strategy " + strategy.getClass().getSimpleName()
								+ " was unsuccessful and could not determine trace feasibility.");
					}
					mRcfgProgramExecution = strategy.getTraceChecker().getRcfgProgramExecution();
					break;
				case UNSAT:
					final IInterpolantGenerator interpolantGenerator = strategy.getInterpolantGenerator();
					InterpolantsPreconditionPostcondition interpolants;
					int iterate;
					if (interpolantGenerator instanceof TraceCheckerSpWp) {
						interpolants = ((TraceCheckerSpWp) interpolantGenerator).getForwardIpp();
						iterate = 2;
					} else {
						interpolants = interpolantGenerator.getIpp();
						iterate = 1;
					}
					
					for (int i = 1; i <= iterate; ++i) {
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
							perfectInterpolantsFound = true;
							// construct interpolant automaton using only this (perfect) sequence
							interpolantSequences = Collections.singletonList(interpolants);
							if (mLogger.isInfoEnabled()) {
								mLogger.info("Found a perfect sequence of interpolants.");
							}
							break;
						}
						interpolantSequences.add(interpolants);
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
					final NestedWordAutomaton<CodeBlock, IPredicate> automaton =
							strategy.getInterpolantAutomatonBuilder(interpolantSequences).getResult();
					mInterpolantAutomaton = automaton;
					
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
	
	private static ManagedScript setupManagedScriptInternal(final IUltimateServiceProvider services,
			final TaCheckAndRefinementPreferences prefs, final BoogieIcfgContainer icfgContainer,
			final IToolchainStorage toolchainStorage, final int iteration) throws AssertionError {
		final ManagedScript managedScript;
		
		switch (prefs.getRefinementStrategy()) {
			case MULTI_TRACK:
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
