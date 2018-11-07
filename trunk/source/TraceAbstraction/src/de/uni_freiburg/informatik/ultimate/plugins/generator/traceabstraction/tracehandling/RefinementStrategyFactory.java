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
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.biesenb.BPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarAbsIntRunner;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPreconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PathProgramCache;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;

/**
 * Factory for obtaining an {@link IRefinementStrategy}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class RefinementStrategyFactory<LETTER extends IIcfgTransition<?>> {
	protected final IUltimateServiceProvider mServices;
	protected final TAPreferences mPrefsConsolidation;
	protected final TaCheckAndRefinementPreferences<LETTER> mPrefs;
	private final CegarAbsIntRunner<LETTER> mAbsIntRunner;
	protected final ILogger mLogger;
	protected final IIcfg<?> mInitialIcfg;
	private final IToolchainStorage mStorage;
	protected final PredicateFactory mPredicateFactory;
	protected final AssertionOrderModulation<LETTER> mAssertionOrderModulation;
	private final PathProgramCache<LETTER> mPathProgramCache;
	private final RefinementStrategy mStrategy;

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
			final IToolchainStorage storage, final TAPreferences taPrefsForInterpolantConsolidation,
			final TaCheckAndRefinementPreferences<LETTER> prefs, final CegarAbsIntRunner<LETTER> absIntRunner,
			final IIcfg<?> initialIcfg, final PredicateFactory predicateFactory,
			final PathProgramCache<LETTER> pathProgramCache) {
		mServices = services;
		mStorage = storage;
		mPrefsConsolidation = taPrefsForInterpolantConsolidation;
		mPrefs = prefs;
		mAbsIntRunner = absIntRunner;
		mLogger = logger;
		mInitialIcfg = initialIcfg;
		mPredicateFactory = predicateFactory;
		mPathProgramCache = pathProgramCache;
		mStrategy = mPrefs.getRefinementStrategy();
		mAssertionOrderModulation = createAssertionOrderModulation(logger, pathProgramCache, mStrategy);
	}

	private AssertionOrderModulation<LETTER> createAssertionOrderModulation(final ILogger logger,
			final PathProgramCache<LETTER> pathProgramCache, final RefinementStrategy strategy) {
		switch (strategy) {
		case CAMEL_NO_AM:
		case MAMMOTH_NO_AM:
		case WARTHOG_NO_AM:
			return new AssertionOrderModulation<>(pathProgramCache, logger, AssertCodeBlockOrder.NOT_INCREMENTALLY);
		case TAIPAN:
			return new AssertionOrderModulation<>(pathProgramCache, logger, AssertCodeBlockOrder.NOT_INCREMENTALLY,
					AssertCodeBlockOrder.OUTSIDE_LOOP_FIRST2, AssertCodeBlockOrder.TERMS_WITH_SMALL_CONSTANTS_FIRST);
		case CAMEL:
		case FIXED_PREFERENCES:
		case LAZY_TAIPAN:
		case PENGUIN:
		case RUBBER_TAIPAN:
		case SMTINTERPOL:
		case TOOTHLESS_TAIPAN:
		case WALRUS:
		case WARTHOG:
		case WOLF:
		case MAMMOTH:
		default:
			logger.info("Using default assertion order modulation");
			return new AssertionOrderModulation<>(pathProgramCache, logger);
		}
	}

	protected IPredicateUnifier getNewPredicateUnifier() {
		final ManagedScript managedScript = mPrefs.getCfgSmtToolkit().getManagedScript();
		final IIcfgSymbolTable symbolTable = mInitialIcfg.getCfgSmtToolkit().getSymbolTable();
		if (mPrefs.usePredicateTrieBasedPredicateUnifier()) {
			return new BPredicateUnifier(mServices, mLogger, managedScript, mPredicateFactory, symbolTable);
		}
		return new PredicateUnifier(mLogger, mServices, managedScript, mPredicateFactory, symbolTable,
				mPrefsConsolidation.getSimplificationTechnique(), mPrefsConsolidation.getXnfConversionTechnique());
	}

	/**
	 * Creates a strategy, e.g., in a new CEGAR loop iteration.
	 *
	 * @param counterexample
	 *            counterexample
	 * @param abstraction
	 *            abstraction
	 * @param iPreconditionProvider
	 * @param benchmark
	 *            benchmark
	 * @return refinement strategy
	 */
	public BaseRefinementStrategy<LETTER> createStrategy(final IRun<LETTER, IPredicate, ?> counterexample,
			final IAutomaton<LETTER, IPredicate> abstraction, final TaskIdentifier taskIdentifier,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory,
			final IPreconditionProvider preconditionProvider) {
		final IPredicateUnifier predicateUnifier = getNewPredicateUnifier();
		final IPredicate precondition = preconditionProvider.constructPrecondition(predicateUnifier);
		mPathProgramCache.addRun(counterexample);

		switch (mStrategy) {
		case FIXED_PREFERENCES:
			final ManagedScript managedScript =
					setupManagedScriptFromPreferences(mServices, mInitialIcfg, mStorage, taskIdentifier, mPrefs);
			return new FixedRefinementStrategy<>(mLogger, mPrefs, managedScript, mServices, mPredicateFactory,
					predicateUnifier, counterexample, precondition, abstraction, mPrefsConsolidation, taskIdentifier,
					emptyStackFactory);
		case PENGUIN:
			return new PenguinRefinementStrategy<>(mLogger, mPrefs, mServices, mInitialIcfg.getCfgSmtToolkit(),
					mPredicateFactory, predicateUnifier, mAssertionOrderModulation, counterexample, precondition,
					abstraction, mPrefsConsolidation, taskIdentifier, emptyStackFactory);
		case CAMEL:
		case CAMEL_NO_AM:
			return new CamelRefinementStrategy<>(mLogger, mPrefs, mServices, mInitialIcfg.getCfgSmtToolkit(),
					mPredicateFactory, predicateUnifier, mAssertionOrderModulation, counterexample, precondition,
					abstraction, mPrefsConsolidation, taskIdentifier, emptyStackFactory);
		case WALRUS:
			return new WalrusRefinementStrategy<>(mLogger, mPrefs, mServices, mInitialIcfg.getCfgSmtToolkit(),
					mPredicateFactory, predicateUnifier, mAssertionOrderModulation, counterexample, precondition,
					abstraction, mPrefsConsolidation, taskIdentifier, emptyStackFactory);
		case WOLF:
			return new WolfRefinementStrategy<>(mLogger, mPrefs, mServices, mInitialIcfg.getCfgSmtToolkit(),
					mPredicateFactory, predicateUnifier, mAssertionOrderModulation, counterexample, precondition,
					abstraction, mPrefsConsolidation, taskIdentifier, emptyStackFactory);
		case WARTHOG_NO_AM:
		case WARTHOG:
			return new WarthogRefinementStrategy<>(mLogger, mPrefs, mServices, mInitialIcfg.getCfgSmtToolkit(),
					mPredicateFactory, predicateUnifier, mAssertionOrderModulation, counterexample, precondition,
					abstraction, mPrefsConsolidation, taskIdentifier, emptyStackFactory);
		case RUBBER_TAIPAN:
			return new RubberTaipanRefinementStrategy<>(mLogger, mServices, mPrefs, mInitialIcfg.getCfgSmtToolkit(),
					mPredicateFactory, predicateUnifier, mAbsIntRunner, mAssertionOrderModulation, counterexample,
					precondition, abstraction, taskIdentifier, emptyStackFactory);
		case TAIPAN:
			return new TaipanRefinementStrategy<>(mLogger, mServices, mPrefs, mInitialIcfg.getCfgSmtToolkit(),
					mPredicateFactory, predicateUnifier, mAbsIntRunner, mAssertionOrderModulation, counterexample,
					precondition, abstraction, taskIdentifier, emptyStackFactory);
		case LAZY_TAIPAN:
			return new LazyTaipanRefinementStrategy<>(mLogger, mServices, mPrefs, mInitialIcfg.getCfgSmtToolkit(),
					mPredicateFactory, predicateUnifier, mAbsIntRunner, mAssertionOrderModulation, counterexample,
					precondition, abstraction, taskIdentifier, emptyStackFactory);
		case TOOTHLESS_TAIPAN:
			return new ToothlessTaipanRefinementStrategy<>(mLogger, mServices, mPrefs, mInitialIcfg.getCfgSmtToolkit(),
					mPredicateFactory, predicateUnifier, mAbsIntRunner, mAssertionOrderModulation, counterexample,
					precondition, abstraction, taskIdentifier, emptyStackFactory);
		case SMTINTERPOL:
			return new SmtInterpolRefinementStrategy<>(mLogger, mPrefs, mServices, mInitialIcfg.getCfgSmtToolkit(),
					mPredicateFactory, predicateUnifier, mAssertionOrderModulation, counterexample, precondition,
					abstraction, mPrefsConsolidation, taskIdentifier, emptyStackFactory);
		case MAMMOTH:
		case MAMMOTH_NO_AM:
			return new MammothRefinementStrategy<>(mLogger, mPrefs, mServices, mInitialIcfg.getCfgSmtToolkit(),
					mPredicateFactory, predicateUnifier, mAssertionOrderModulation, counterexample, precondition,
					abstraction, mPrefsConsolidation, taskIdentifier, emptyStackFactory);
		default:
			throw new IllegalArgumentException(
					"Unknown refinement strategy specified: " + mPrefs.getRefinementStrategy());
		}
	}

	private ManagedScript setupManagedScriptFromPreferences(final IUltimateServiceProvider services,
			final IIcfg<?> icfgContainer, final IToolchainStorage toolchainStorage, final TaskIdentifier taskIdentifier,
			final TaCheckAndRefinementPreferences<LETTER> prefs) throws AssertionError {
		final ManagedScript mgdScriptTc;
		if (prefs.getUseSeparateSolverForTracechecks()) {
			final String filename = taskIdentifier + "_TraceCheck";
			final SolverMode solverMode = prefs.getSolverMode();
			final boolean fakeNonIncrementalSolver = prefs.getFakeNonIncrementalSolver();
			final String commandExternalSolver = prefs.getCommandExternalSolver();
			final boolean dumpSmtScriptToFile = prefs.getDumpSmtScriptToFile();
			final String pathOfDumpedScript = prefs.getPathOfDumpedScript();
			final SolverSettings solverSettings = SolverBuilder.constructSolverSettings(filename, solverMode,
					fakeNonIncrementalSolver, commandExternalSolver, dumpSmtScriptToFile, pathOfDumpedScript);
			final Script tcSolver = SolverBuilder.buildAndInitializeSolver(services, toolchainStorage,
					prefs.getSolverMode(), solverSettings, false, false, prefs.getLogicForExternalSolver(), filename);
			mgdScriptTc = new ManagedScript(services, tcSolver);
			icfgContainer.getCfgSmtToolkit().getSmtSymbols().transferSymbols(tcSolver);
		} else {
			mgdScriptTc = prefs.getCfgSmtToolkit().getManagedScript();
		}
		return mgdScriptTc;
	}

	public PathProgramCache<LETTER> getPathProgramCache() {
		return mPathProgramCache;
	}
}
