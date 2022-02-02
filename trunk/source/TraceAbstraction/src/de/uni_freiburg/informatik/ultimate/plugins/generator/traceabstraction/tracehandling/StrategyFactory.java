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
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.biesenb.BPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngine;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPostconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPreconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PathProgramCache;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.BadgerRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.BearRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.CamelNoAmRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.CamelRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.CamelSmtAmRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.DachshundRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.FixedRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.LazyTaipanRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.LizardRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.MammothNoAmRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.MammothRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.McrRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.PenguinRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.RubberTaipanRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.SifaTaipanRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.SmtInterpolRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.TaipanRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.ToothlessSifaTaipanRefinementStrategy;
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
public class StrategyFactory<L extends IIcfgTransition<?>> {
	private final TAPreferences mTaPrefs;
	private final TaCheckAndRefinementPreferences<L> mPrefs;
	private final ILogger mLogger;
	private final IIcfg<?> mInitialIcfg;
	private final PredicateFactory mPredicateFactory;
	private final PredicateFactoryForInterpolantAutomata mPredicateFactoryInterpolAut;
	private final PathProgramCache<L> mPathProgramCache;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final Class<L> mTransitionClazz;

	public StrategyFactory(final ILogger logger, final TAPreferences taPrefsForInterpolantConsolidation,
			final TaCheckAndRefinementPreferences<L> prefs, final IIcfg<?> initialIcfg,
			final PredicateFactory predicateFactory, final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolAut,
			final Class<L> transitionClazz) {
		mLogger = logger;
		mTaPrefs = taPrefsForInterpolantConsolidation;
		mPrefs = prefs;
		mInitialIcfg = initialIcfg;
		mCfgSmtToolkit = initialIcfg.getCfgSmtToolkit();
		mPredicateFactory = predicateFactory;
		mPredicateFactoryInterpolAut = predicateFactoryInterpolAut;
		mPathProgramCache = new PathProgramCache<>(mLogger);
		mTransitionClazz = transitionClazz;
	}

	public PathProgramCache<L> getPathProgramCache() {
		return mPathProgramCache;
	}

	/**
	 * Constructs a {@link IRefinementStrategy} that can be used in conjunction with a {@link IRefinementEngine}.
	 */
	public IRefinementStrategy<L> constructStrategy(final IUltimateServiceProvider services,
			final IRun<L, ?> counterexample, final IAutomaton<L, IPredicate> abstraction,
			final TaskIdentifier taskIdentifier, final IEmptyStackStateFactory<IPredicate> emptyStackFactory,
			final IPreconditionProvider preconditionProvider, final IPostconditionProvider postconditionProvider) {
		return constructStrategy(services, counterexample, abstraction, taskIdentifier, emptyStackFactory,
				preconditionProvider, postconditionProvider, mPrefs.getRefinementStrategy());
	}

	/**
	 * Constructs a {@link IRefinementStrategy} that can be used in conjunction with a {@link IRefinementEngine}.
	 */
	public IRefinementStrategy<L> constructStrategy(final IUltimateServiceProvider services,
			final IRun<L, ?> counterexample, final IAutomaton<L, IPredicate> abstraction,
			final TaskIdentifier taskIdentifier, final IEmptyStackStateFactory<IPredicate> emptyStackFactory,
			final IPreconditionProvider preconditionProvider, final IPostconditionProvider postconditionProvider,
			final RefinementStrategy strategyType) {

		final IPredicateUnifier predicateUnifier = constructPredicateUnifier(services);
		final IPredicate precondition = preconditionProvider.constructPrecondition(predicateUnifier);
		final IPredicate postcondition = postconditionProvider.constructPostcondition(predicateUnifier);
		mPathProgramCache.addRun(counterexample);

		final StrategyModuleFactory<L> strategyModuleFactory = new StrategyModuleFactory<>(taskIdentifier, services,
				mLogger, mPrefs, mTaPrefs, counterexample, precondition, postcondition, predicateUnifier,
				mPredicateFactory, abstraction, emptyStackFactory, mCfgSmtToolkit, mPredicateFactoryInterpolAut,
				mPathProgramCache, mTransitionClazz);
		final RefinementStrategyExceptionBlacklist exceptionBlacklist = mPrefs.getExceptionBlacklist();

		switch (strategyType) {
		case FIXED_PREFERENCES:
			return new FixedRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case PENGUIN:
			return new PenguinRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case CAMEL:
			return new CamelRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case CAMEL_NO_AM:
			return new CamelNoAmRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case CAMEL_SMT_AM:
			return new CamelSmtAmRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case LIZARD:
			return new LizardRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case BADGER:
			return new BadgerRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case WALRUS:
			return new WalrusRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case WOLF:
			return new WolfRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case BEAR:
			return new BearRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case WARTHOG_NO_AM:
			return new WarthogNoAmRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case WARTHOG:
			return new WarthogRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case RUBBER_TAIPAN:
			return new RubberTaipanRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case TAIPAN:
			return new TaipanRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case LAZY_TAIPAN:
			return new LazyTaipanRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case TOOTHLESS_TAIPAN:
			return new ToothlessTaipanRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case SMTINTERPOL:
			return new SmtInterpolRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case MAMMOTH:
			return new MammothRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case MAMMOTH_NO_AM:
			return new MammothNoAmRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case DACHSHUND:
			return new DachshundRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case SIFA_TAIPAN:
			return new SifaTaipanRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case TOOTHLESS_SIFA_TAIPAN:
			return new ToothlessSifaTaipanRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case MCR:
			return new McrRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist, this);
		default:
			throw new IllegalArgumentException(
					"Unknown refinement strategy specified: " + mPrefs.getRefinementStrategy());
		}
	}

	private IPredicateUnifier constructPredicateUnifier(final IUltimateServiceProvider services) {
		final ManagedScript managedScript = mPrefs.getCfgSmtToolkit().getManagedScript();
		final IIcfgSymbolTable symbolTable = mInitialIcfg.getCfgSmtToolkit().getSymbolTable();
		if (mPrefs.usePredicateTrieBasedPredicateUnifier()) {
			return new BPredicateUnifier(services, mLogger, managedScript, mPredicateFactory, symbolTable);
		}
		return new PredicateUnifier(mLogger, services, managedScript, mPredicateFactory, symbolTable,
				mTaPrefs.getSimplificationTechnique(), mTaPrefs.getXnfConversionTechnique());
	}

}
