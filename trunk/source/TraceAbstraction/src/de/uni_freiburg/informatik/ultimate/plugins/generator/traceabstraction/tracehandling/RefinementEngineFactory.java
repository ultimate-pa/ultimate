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

import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.biesenb.BPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPreconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PathProgramCache;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.BadgerRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.CamelNoAmRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.CamelRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.FixedRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.LazyTaipanRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.MammothNoAmRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.MammothRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.PenguinRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.RubberTaipanRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.SmtInterpolRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.TaipanRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.ToothlessTaipanRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.WalrusRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.WarthogNoAmRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.WarthogRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.WolfRefinementStrategy;

/**
 * Factory for obtaining an {@link IRefinementStrategy}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class RefinementEngineFactory<LETTER extends IIcfgTransition<?>> {
	private final IUltimateServiceProvider mServices;
	private final TAPreferences mTaPrefs;
	private final TaCheckAndRefinementPreferences<LETTER> mPrefs;
	private final ILogger mLogger;
	private final IIcfg<?> mInitialIcfg;
	private final PredicateFactory mPredicateFactory;
	private final PredicateFactoryForInterpolantAutomata mPredicateFactoryInterpolAut;
	private final PathProgramCache<LETTER> mPathProgramCache;
	private final RefinementStrategy mStrategy;
	private final Function<IPredicateUnifier, IHoareTripleChecker> mFunHtcConstructor;
	private final CfgSmtToolkit mCfgSmtToolkit;

	public RefinementEngineFactory(final ILogger logger, final IUltimateServiceProvider services,
			final TAPreferences taPrefsForInterpolantConsolidation, final TaCheckAndRefinementPreferences<LETTER> prefs,
			final IIcfg<?> initialIcfg, final PredicateFactory predicateFactory,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolAut) {
		mServices = services;
		mLogger = logger;
		mTaPrefs = taPrefsForInterpolantConsolidation;
		mPrefs = prefs;
		mInitialIcfg = initialIcfg;
		mCfgSmtToolkit = initialIcfg.getCfgSmtToolkit();
		mPredicateFactory = predicateFactory;
		mPredicateFactoryInterpolAut = predicateFactoryInterpolAut;
		mFunHtcConstructor = pu -> TraceAbstractionUtils.constructEfficientHoareTripleCheckerWithCaching(mServices,
				mTaPrefs.getHoareTripleChecks(), mCfgSmtToolkit, pu);
		mPathProgramCache = new PathProgramCache<>(mLogger);

		mStrategy = mPrefs.getRefinementStrategy();
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
	public IRefinementEngine<NestedWordAutomaton<LETTER, IPredicate>> runRefinementEngine(
			final IRun<LETTER, IPredicate, ?> counterexample, final IAutomaton<LETTER, IPredicate> abstraction,
			final TaskIdentifier taskIdentifier, final IEmptyStackStateFactory<IPredicate> emptyStackFactory,
			final IPreconditionProvider preconditionProvider) {
		final IPredicateUnifier predicateUnifier = getNewPredicateUnifier();
		final IRefinementStrategy<LETTER> strategy = createStrategy(counterexample, abstraction, taskIdentifier,
				emptyStackFactory, preconditionProvider, predicateUnifier);
		return new TraceAbstractionRefinementEngine<>(mLogger, predicateUnifier, strategy, mFunHtcConstructor);
	}

	public PathProgramCache<LETTER> getPathProgramCache() {
		return mPathProgramCache;
	}

	private IRefinementStrategy<LETTER> createStrategy(final IRun<LETTER, IPredicate, ?> counterexample,
			final IAutomaton<LETTER, IPredicate> abstraction, final TaskIdentifier taskIdentifier,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory,
			final IPreconditionProvider preconditionProvider, final IPredicateUnifier predicateUnifier) {

		final IPredicate precondition = preconditionProvider.constructPrecondition(predicateUnifier);
		mPathProgramCache.addRun(counterexample);

		final StrategyModuleFactory<LETTER> strategyModuleFactory = new StrategyModuleFactory<>(taskIdentifier,
				mServices, mLogger, mPrefs, mTaPrefs, counterexample, precondition, predicateUnifier, mPredicateFactory,
				abstraction, emptyStackFactory, mCfgSmtToolkit, mPredicateFactoryInterpolAut, mPathProgramCache);

		switch (mStrategy) {
		case FIXED_PREFERENCES:
			return new FixedRefinementStrategy<>(strategyModuleFactory, mPrefs.getExceptionBlacklist());
		case PENGUIN:
			return new PenguinRefinementStrategy<>(strategyModuleFactory, mPrefs.getExceptionBlacklist());
		case CAMEL:
			return new CamelRefinementStrategy<>(strategyModuleFactory, mPrefs.getExceptionBlacklist());
		case CAMEL_NO_AM:
			return new CamelNoAmRefinementStrategy<>(strategyModuleFactory, mPrefs.getExceptionBlacklist());
		case BADGER:
			return new BadgerRefinementStrategy<>(strategyModuleFactory, mPrefs.getExceptionBlacklist());
		case WALRUS:
			return new WalrusRefinementStrategy<>(strategyModuleFactory, mPrefs.getExceptionBlacklist());
		case WOLF:
			return new WolfRefinementStrategy<>(strategyModuleFactory, mPrefs.getExceptionBlacklist());
		case WARTHOG_NO_AM:
			return new WarthogNoAmRefinementStrategy<>(strategyModuleFactory, mPrefs.getExceptionBlacklist());
		case WARTHOG:
			return new WarthogRefinementStrategy<>(strategyModuleFactory, mPrefs.getExceptionBlacklist());
		case RUBBER_TAIPAN:
			return new RubberTaipanRefinementStrategy<>(strategyModuleFactory, mPrefs.getExceptionBlacklist());
		case TAIPAN:
			return new TaipanRefinementStrategy<>(strategyModuleFactory, mPrefs.getExceptionBlacklist());
		case LAZY_TAIPAN:
			return new LazyTaipanRefinementStrategy<>(strategyModuleFactory, mPrefs.getExceptionBlacklist());
		case TOOTHLESS_TAIPAN:
			return new ToothlessTaipanRefinementStrategy<>(strategyModuleFactory, mPrefs.getExceptionBlacklist());
		case SMTINTERPOL:
			return new SmtInterpolRefinementStrategy<>(strategyModuleFactory, mPrefs.getExceptionBlacklist());
		case MAMMOTH:
			return new MammothRefinementStrategy<>(strategyModuleFactory, mPrefs.getExceptionBlacklist());
		case MAMMOTH_NO_AM:
			return new MammothNoAmRefinementStrategy<>(strategyModuleFactory, mPrefs.getExceptionBlacklist());
		default:
			throw new IllegalArgumentException(
					"Unknown refinement strategy specified: " + mPrefs.getRefinementStrategy());
		}
	}

	private IPredicateUnifier getNewPredicateUnifier() {
		final ManagedScript managedScript = mPrefs.getCfgSmtToolkit().getManagedScript();
		final IIcfgSymbolTable symbolTable = mInitialIcfg.getCfgSmtToolkit().getSymbolTable();
		if (mPrefs.usePredicateTrieBasedPredicateUnifier()) {
			return new BPredicateUnifier(mServices, mLogger, managedScript, mPredicateFactory, symbolTable);
		}
		return new PredicateUnifier(mLogger, mServices, managedScript, mPredicateFactory, symbolTable,
				mTaPrefs.getSimplificationTechnique(), mTaPrefs.getXnfConversionTechnique());
	}

}
