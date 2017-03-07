/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.interactive.IInteractive;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarAbsIntRunner;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.interactive.ParrotInteractiveIterationInfo;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.interactive.ParrotRefinementStrategy;

/**
 * Factory for obtaining an {@link IRefinementStrategy}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class RefinementStrategyFactory<LETTER extends IIcfgTransition<?>> {
	private final IUltimateServiceProvider mServices;
	private final TAPreferences mPrefsConsolidation;
	private final TaCheckAndRefinementPreferences<LETTER> mPrefs;
	private final CegarAbsIntRunner<LETTER> mAbsIntRunner;
	private final ILogger mLogger;
	private final IIcfg<?> mInitialIcfg;
	private final IToolchainStorage mStorage;
	private final PredicateFactory mPredicateFactory;
	private final AssertionOrderModulation<LETTER> mAssertionOrderModulation;
	private final IInteractive<Object> mInteractive;
	private final ParrotInteractiveIterationInfo mParrotInteractiveIterationInfo;

	/**
	 * @param logger
	 *            Logger.
	 * @param services
	 *            Ultimate services
	 * @param storage
	 *            toolchain storage
	 * @param taPrefsForInterpolantConsolidation
	 *            TODO Matthias wants to get rid of this
	 * @param prefs
	 *            preferences
	 * @param absIntRunner
	 *            abstract interpretation runner
	 * @param initialIcfg
	 *            initial ICFG
	 * @param predicateFactory
	 *            predicate factory
	 */
	public RefinementStrategyFactory(final ILogger logger, final IUltimateServiceProvider services,
			final IInteractive<Object> interactive,
			final IToolchainStorage storage, final TAPreferences taPrefsForInterpolantConsolidation,
			final TaCheckAndRefinementPreferences<LETTER> prefs, final CegarAbsIntRunner<LETTER> absIntRunner,
			final IIcfg<?> initialIcfg, final PredicateFactory predicateFactory) {
		mServices = services;
		mStorage = storage;
		mPrefsConsolidation = taPrefsForInterpolantConsolidation;
		mPrefs = prefs;
		mAbsIntRunner = absIntRunner;
		mLogger = logger;
		mInitialIcfg = initialIcfg;
		mPredicateFactory = predicateFactory;
		mAssertionOrderModulation = new AssertionOrderModulation<>();
		mInteractive = interactive;
		if (mInteractive == null) {
			mParrotInteractiveIterationInfo = null;
		} else {
			mParrotInteractiveIterationInfo = new ParrotInteractiveIterationInfo();
		}
	}

	/**
	 * Creates a strategy, e.g., in a new CEGAR loop iteration.
	 *
	 * @param counterexample
	 *            counterexample
	 * @param abstraction
	 *            abstraction
	 * @param iteration
	 *            current iteration
	 * @param benchmark
	 *            benchmark
	 * @return refinement strategy
	 */
	public IRefinementStrategy<LETTER> createStrategy(final RefinementStrategy strategy,
			final IRun<LETTER, IPredicate, ?> counterexample, final IAutomaton<LETTER, IPredicate> abstraction,
			final int iteration, final CegarLoopStatisticsGenerator benchmark) {
		final PredicateUnifier predicateUnifier = new PredicateUnifier(mServices,
				mPrefs.getCfgSmtToolkit().getManagedScript(), mPredicateFactory,
				mInitialIcfg.getCfgSmtToolkit().getSymbolTable(), mPrefsConsolidation.getSimplificationTechnique(),
				mPrefsConsolidation.getXnfConversionTechnique());

		switch (strategy) {
		case FIXED_PREFERENCES:
			final ManagedScript managedScript =
					setupManagedScriptFromPreferences(mServices, mInitialIcfg, mStorage, iteration, mPrefs);
			return new FixedTraceAbstractionRefinementStrategy<>(mLogger, mPrefs, managedScript, mServices,
					mPredicateFactory, predicateUnifier, counterexample, abstraction, mPrefsConsolidation, iteration,
					benchmark);
		case PENGUIN:
			return new PenguinRefinementStrategy<>(mLogger, mPrefs, mServices, mInitialIcfg.getCfgSmtToolkit(),
					mPredicateFactory, predicateUnifier, mAssertionOrderModulation, counterexample, abstraction,
					mPrefsConsolidation, iteration, benchmark);
		case CAMEL:
			return new CamelRefinementStrategy<>(mLogger, mPrefs, mServices, mInitialIcfg.getCfgSmtToolkit(),
					mPredicateFactory, predicateUnifier, mAssertionOrderModulation, counterexample, abstraction,
					mPrefsConsolidation, iteration, benchmark);
		case WALRUS:
			return new WalrusRefinementStrategy<>(mLogger, mPrefs, mServices, mInitialIcfg.getCfgSmtToolkit(),
					mPredicateFactory, predicateUnifier, mAssertionOrderModulation, counterexample, abstraction,
					mPrefsConsolidation, iteration, benchmark);
		case WOLF:
			return new WolfRefinementStrategy<>(mLogger, mPrefs, mServices, mInitialIcfg.getCfgSmtToolkit(),
					mPredicateFactory, predicateUnifier, mAssertionOrderModulation, counterexample, abstraction,
					mPrefsConsolidation, iteration, benchmark);
		case RUBBER_TAIPAN:
			return new RubberTaipanRefinementStrategy<>(mLogger, mServices, mPrefs, mInitialIcfg.getCfgSmtToolkit(),
					mPredicateFactory, predicateUnifier, mAbsIntRunner, mAssertionOrderModulation, counterexample,
					abstraction, iteration, benchmark);
		case TAIPAN:
			return new TaipanRefinementStrategy<>(mLogger, mServices, mPrefs, mInitialIcfg.getCfgSmtToolkit(),
					mPredicateFactory, predicateUnifier, mAbsIntRunner, mAssertionOrderModulation, counterexample,
					abstraction, iteration, benchmark);
		case PARROT:
			if (mInteractive == null) {
				throw new IllegalArgumentException(
						"Interactive strategy chosen, but interface available. Please start ultimate in Interactive mode.");
			}
			return new ParrotRefinementStrategy<LETTER>(mLogger, mPrefs, mServices, mInitialIcfg.getCfgSmtToolkit(),
					mPredicateFactory, predicateUnifier, mAssertionOrderModulation, counterexample, abstraction,
					mPrefsConsolidation, iteration, benchmark) {
				@Override
				protected IInteractive<Object> getInteractive() {
					// instead of passing the interactive interface via
					// constructor, it is necessary to have a getter
					// because .next() is called in the constructor of the
					// superclass.
					return mInteractive;
				}

				@Override
				protected IRefinementStrategy<LETTER> createFallbackStrategy(RefinementStrategy strategy) {
					return createStrategy(strategy, counterexample, abstraction, iteration, benchmark);
				}

				@Override
				protected ParrotInteractiveIterationInfo getIterationInfo() {
					return mParrotInteractiveIterationInfo;
				};

			};
		default:
			throw new IllegalArgumentException(
					"Unknown refinement strategy specified: " + mPrefs.getRefinementStrategy());
		}
	}

	private ManagedScript setupManagedScriptFromPreferences(final IUltimateServiceProvider services,
			final IIcfg<?> icfgContainer, final IToolchainStorage toolchainStorage, final int iteration,
			final TaCheckAndRefinementPreferences<LETTER> prefs) throws AssertionError {
		final ManagedScript mgdScriptTc;
		if (prefs.getUseSeparateSolverForTracechecks()) {
			final String filename = icfgContainer.getIdentifier() + "_TraceCheck_Iteration" + iteration;
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
			final Term axioms = icfgContainer.getCfgSmtToolkit().getAxioms().getFormula();
			tcSolver.assertTerm(tt.transform(axioms));
		} else {
			mgdScriptTc = prefs.getCfgSmtToolkit().getManagedScript();
		}
		return mgdScriptTc;
	}
}
