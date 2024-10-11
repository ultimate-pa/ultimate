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
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.AcceleratedInterpolationCore.IStrategySupplier;
import de.uni_freiburg.informatik.ultimate.lib.mcr.IInterpolantProvider;
import de.uni_freiburg.informatik.ultimate.lib.mcr.SpInterpolantProvider;
import de.uni_freiburg.informatik.ultimate.lib.mcr.WpInterpolantProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.biesenb.BPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IIpTcStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngine;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.TermClassifier;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPostconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPreconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PathProgramCache;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.AcceleratedInterpolationRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.AcceleratedTraceCheckRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.BadgerRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.BearRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.CamelNoAmRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy.CamelOnlyBpRefinementStrategy;
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
			final PredicateFactory predicateFactory,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolAut, final Class<L> transitionClazz) {
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
	public ITARefinementStrategy<L> constructStrategy(final IUltimateServiceProvider services,
			final IRun<L, ?> counterexample, final IAutomaton<L, IPredicate> abstraction,
			final TaskIdentifier taskIdentifier, final IEmptyStackStateFactory<IPredicate> emptyStackFactory,
			final IPreconditionProvider preconditionProvider, final IPostconditionProvider postconditionProvider) {
		final IPredicateUnifier predicateUnifier = constructPredicateUnifier(services);
		final IPredicate precondition = preconditionProvider.constructPrecondition(predicateUnifier);
		final IPredicate postcondition = postconditionProvider.constructPostcondition(predicateUnifier);
		return constructStrategy(services, counterexample, abstraction, taskIdentifier, emptyStackFactory,
				predicateUnifier, precondition, postcondition, mPrefs.getRefinementStrategy());
	}

	/**
	 * Constructs a {@link IRefinementStrategy} that can be used in conjunction with a {@link IRefinementEngine}.
	 */
	public ITARefinementStrategy<L> constructStrategy(final IUltimateServiceProvider services,
			final IRun<L, ?> counterexample, final IAutomaton<L, IPredicate> abstraction,
			final TaskIdentifier taskIdentifier, final IEmptyStackStateFactory<IPredicate> emptyStackFactory,
			final IPredicateUnifier predicateUnifier, final IPredicate precondition,
			final IPredicate postcondition, final RefinementStrategy strategyType) {

		mPathProgramCache.addRun(counterexample);

		final StrategyModuleFactory strategyModuleFactory = new StrategyModuleFactory(taskIdentifier, services,
				counterexample, precondition, postcondition, predicateUnifier, abstraction, emptyStackFactory);
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
		case CAMEL_BP_ONLY:
			return new CamelOnlyBpRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
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
		case ACCELERATED_INTERPOLATION:
			return new AcceleratedInterpolationRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
		case ACCELERATED_TRACE_CHECK:
			return new AcceleratedTraceCheckRefinementStrategy<>(strategyModuleFactory, exceptionBlacklist);
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
				mTaPrefs.getSimplificationTechnique());
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 * @param <L>
	 */
	public class StrategyModuleFactory {

		private final TaskIdentifier mTaskIdentifier;
		private final IUltimateServiceProvider mServices;
		private final IRun<L, ?> mCounterexample;
		private final IPredicateUnifier mPredicateUnifier;
		private final IPredicate mPrecondition;
		private final IPredicate mPostcondition;
		private final IAutomaton<L, IPredicate> mAbstraction;
		private final IEmptyStackStateFactory<IPredicate> mEmptyStackFactory;

		public StrategyModuleFactory(final TaskIdentifier taskIdentifier, final IUltimateServiceProvider services,
				final IRun<L, ?> counterExample, final IPredicate precondition, final IPredicate postcondition,
				final IPredicateUnifier predicateUnifier, final IAutomaton<L, IPredicate> abstraction,
				final IEmptyStackStateFactory<IPredicate> emptyStackFactory) {
			mServices = services;
			mCounterexample = counterExample;
			mPredicateUnifier = predicateUnifier;
			mPrecondition = precondition;
			mPostcondition = postcondition;
			mTaskIdentifier = taskIdentifier;
			mAbstraction = abstraction;
			mEmptyStackFactory = emptyStackFactory;
		}

		public StrategyModuleMcr<L> createStrategyModuleMcr(final StrategyFactory<L> strategyFactory) {
			isOnlyDefaultPrePostConditions();
			final boolean useInterpolantConsolidation = mPrefs.getUseInterpolantConsolidation();
			if (useInterpolantConsolidation) {
				throw new UnsupportedOperationException("Interpolant consolidation and MCR cannot be combined");
			}
			return new StrategyModuleMcr<>(mServices, mLogger, mPrefs, mPredicateUnifier, mEmptyStackFactory,
					strategyFactory, mCounterexample, mAbstraction, mTaskIdentifier, createMcrInterpolantProvider());
		}

		public IIpTcStrategyModule<?, L> createIpTcStrategyModuleAcceleratedInterpolation() {
			isOnlyDefaultPrePostConditions();
			final boolean useInterpolantConsolidation = mPrefs.getUseInterpolantConsolidation();
			if (useInterpolantConsolidation) {
				throw new UnsupportedOperationException(
						"Interpolant consolidation and AcceleratedInterpolation cannot be combined");
			}
			final RefinementStrategy nestedStrategy = mPrefs.getAcceleratedInterpolationRefinementStrategy();
			final IStrategySupplier<L> strategySupplier =
					run -> constructStrategy(mServices, run, mAbstraction, mTaskIdentifier, mEmptyStackFactory,
							mPredicateUnifier, mPrecondition, mPostcondition, nestedStrategy);

			return new IpTcStrategyModuleAcceleratedInterpolation<>(mServices, mLogger, mCounterexample,
					mPredicateUnifier, mPrefs, strategySupplier, mTransitionClazz);
		}

		public IIpTcStrategyModule<?, L> createIpTcStrategyModuleAcceleratedTraceCheck() {
			isOnlyDefaultPrePostConditions();
			final boolean useInterpolantConsolidation = mPrefs.getUseInterpolantConsolidation();
			if (useInterpolantConsolidation) {
				throw new UnsupportedOperationException(
						"Interpolant consolidation and AcceleratedInterpolation cannot be combined");
			}
			return new IpTcStrategyModuleAcceleratedTraceCheck<>(mServices, mLogger, mCounterexample, mPrecondition,
					mPostcondition, mPredicateUnifier, mPrefs, mPredicateFactory);
		}

		public IIpTcStrategyModule<?, L> createIpTcStrategyModuleSmtInterpolCraig(
				final InterpolationTechnique technique, final AssertCodeBlockOrder... order) {
			return createIpTcStrategyModuleSmtInterpolCraig(-1, technique, order);
		}

		public IIpTcStrategyModule<?, L> createIpTcStrategyModuleSmtInterpolCraig(final long timeoutInMillis,
				final InterpolationTechnique technique, final AssertCodeBlockOrder... order) {
			return createModuleWrapperIfNecessary(new IpTcStrategyModuleSmtInterpolCraig<>(mTaskIdentifier, mServices,
					mPrefs, mCounterexample, mPrecondition, mPostcondition,
					new AssertionOrderModulation<>(mPathProgramCache, mLogger, order), mPredicateUnifier,
					mPredicateFactory, timeoutInMillis, technique));
		}

		public IIpTcStrategyModule<?, L> createIpTcStrategyModuleSmtInterpolSpWp(final InterpolationTechnique technique,
				final AssertCodeBlockOrder... order) {
			return createIpTcStrategyModuleSmtInterpolSpWp(-1, technique, order);
		}

		public IIpTcStrategyModule<?, L> createIpTcStrategyModuleSmtInterpolSpWp(final long timeoutInMillis,
				final InterpolationTechnique technique, final AssertCodeBlockOrder... order) {
			return createModuleWrapperIfNecessary(new IpTcStrategyModuleSmtInterpolSpWp<>(mTaskIdentifier, mServices,
					mPrefs, mCounterexample, mPrecondition, mPostcondition,
					new AssertionOrderModulation<>(mPathProgramCache, mLogger, order), mPredicateUnifier,
					mPredicateFactory, timeoutInMillis, technique));
		}

		public IIpTcStrategyModule<?, L> createIpTcStrategyModuleZ3(final InterpolationTechnique technique,
				final AssertCodeBlockOrder... order) {
			return createIpTcStrategyModuleZ3(-1, technique, order);
		}

		public IIpTcStrategyModule<?, L> createIpTcStrategyModuleZ3(final long timeoutInMillis,
				final InterpolationTechnique technique, final AssertCodeBlockOrder... order) {
			return createModuleWrapperIfNecessary(
					new IpTcStrategyModuleZ3<>(mTaskIdentifier, mServices, mPrefs, mCounterexample, mPrecondition,
							mPostcondition, new AssertionOrderModulation<>(mPathProgramCache, mLogger, order),
							mPredicateUnifier, mPredicateFactory, timeoutInMillis, technique));
		}

		public IIpTcStrategyModule<?, L> createIpTcStrategyModuleMathsat(final InterpolationTechnique technique,
				final AssertCodeBlockOrder... order) {
			return createModuleWrapperIfNecessary(
					new IpTcStrategyModuleMathsat<>(mTaskIdentifier, mServices, mPrefs, mCounterexample, mPrecondition,
							mPostcondition, new AssertionOrderModulation<>(mPathProgramCache, mLogger, order),
							mPredicateUnifier, mPredicateFactory, technique));
		}

		public IIpTcStrategyModule<?, L> createIpTcStrategyModuleCVC4(final InterpolationTechnique technique,
				final AssertCodeBlockOrder... order) {
			return createIpTcStrategyModuleCVC4(-1, technique, order);
		}

		public IIpTcStrategyModule<?, L> createIpTcStrategyModuleCVC4(final long timeoutInMillis,
				final InterpolationTechnique technique, final AssertCodeBlockOrder... order) {
			return createModuleWrapperIfNecessary(
					new IpTcStrategyModuleCvc4<>(mTaskIdentifier, mServices, mPrefs, mCounterexample, mPrecondition,
							mPostcondition, new AssertionOrderModulation<>(mPathProgramCache, mLogger, order),
							mPredicateUnifier, mPredicateFactory, timeoutInMillis, technique));
		}

		public IIpTcStrategyModule<?, L> createIpTcStrategyModuleCVC5(final InterpolationTechnique technique,
				final AssertCodeBlockOrder... order) {
			return createIpTcStrategyModuleCVC5(-1, technique, order);
		}

		public IIpTcStrategyModule<?, L> createIpTcStrategyModuleCVC5(final long timeoutInMillis,
				final InterpolationTechnique technique, final AssertCodeBlockOrder... order) {
			return createModuleWrapperIfNecessary(
					new IpTcStrategyModuleCvc5<>(mTaskIdentifier, mServices, mPrefs, mCounterexample, mPrecondition,
							mPostcondition, new AssertionOrderModulation<>(mPathProgramCache, mLogger, order),
							mPredicateUnifier, mPredicateFactory, timeoutInMillis, technique));
		}

		public IIpTcStrategyModule<?, L> createIpTcStrategyModuleAbstractInterpretation() {
			isOnlyDefaultPrePostConditions();
			return createModuleWrapperIfNecessary(new IpTcStrategyModuleAbstractInterpretation<>(mCounterexample,
					mPredicateUnifier, mServices, mPrefs.getIcfgContainer(), mPathProgramCache, mTaPrefs));
		}

		public IIpTcStrategyModule<?, L> createIpTcStrategyModuleSifa() {
			isOnlyDefaultPrePostConditions();
			return createModuleWrapperIfNecessary(new IpTcStrategyModuleSifa<>(mServices, mLogger,
					mPrefs.getIcfgContainer(), mCounterexample, mPredicateUnifier));
		}

		public IIpTcStrategyModule<?, L> createIpTcStrategyModulePdr() {
			return createModuleWrapperIfNecessary(new IpTcStrategyModulePdr<>(mServices, mLogger, mPrecondition,
					mPostcondition, mCounterexample, mPredicateUnifier, mPrefs, mTransitionClazz));
		}

		public IIpTcStrategyModule<?, L> createIpTcStrategyModulePreferences() {
			return createModuleWrapperIfNecessary(new IpTcStrategyModulePreferences<>(mTaskIdentifier, mServices,
					mPrefs, mCounterexample, mPrecondition, mPostcondition,
					new AssertionOrderModulation<>(mPathProgramCache, mLogger, mPrefs.getAssertCodeBlockOrder()),
					mPredicateUnifier, mPredicateFactory, mTransitionClazz));
		}

		private IIpTcStrategyModule<?, L>
				createModuleWrapperIfNecessary(final IIpTcStrategyModule<?, L> trackStrategyModule) {
			final boolean useInterpolantConsolidation = mPrefs.getUseInterpolantConsolidation();
			if (useInterpolantConsolidation) {
				isOnlyDefaultPrePostConditions();
				return new IpTcStrategyModuleInterpolantConsolidation<>(mServices, mLogger, mPrefs, mPredicateFactory,
						trackStrategyModule);
			}
			return trackStrategyModule;
		}

		public IIpAbStrategyModule<L> createInterpolantAutomatonBuilderStrategyModulePreferences(
				final IIpTcStrategyModule<?, L> preferenceIpTc) {
			return createInterpolantAutomatonBuilderStrategyModulePreferences(mTaPrefs.interpolantAutomaton(),
					preferenceIpTc);
		}

		@SuppressWarnings("unchecked")
		private IIpAbStrategyModule<L> createInterpolantAutomatonBuilderStrategyModulePreferences(
				final InterpolantAutomaton setting, final IIpTcStrategyModule<?, L> preferenceIpTc) {
			final InterpolantAutomaton realSetting =
					mTaPrefs.overrideInterpolantAutomaton() ? mTaPrefs.interpolantAutomaton() : setting;
			switch (realSetting) {
			case STRAIGHT_LINE:
				return new IpAbStrategyModuleStraightlineAll<>(mServices, mLogger, mAbstraction, mCounterexample,
						mEmptyStackFactory);
			case CANONICAL:
				return new IpAbStrategyModuleCanonical<>(mServices, mLogger, mAbstraction, mCounterexample,
						mEmptyStackFactory, mPredicateUnifier);
			case TOTALINTERPOLATION2:
				return new IpAbStrategyModuleTotalInterpolation<>(mServices, mAbstraction, mCounterexample,
						mPredicateUnifier, mPrefs, mCfgSmtToolkit, mPredicateFactoryInterpolAut);
			case ABSTRACT_INTERPRETATION:
				final IIpTcStrategyModule<?, L> strategy =
						preferenceIpTc == null ? createIpTcStrategyModulePreferences() : preferenceIpTc;
				return new IpAbStrategyModuleAbstractInterpretation<>(mAbstraction, mCounterexample, mPredicateUnifier,
						(IpTcStrategyModuleAbstractInterpretation<L>) strategy, mEmptyStackFactory);
			case MCR:
				return new IpAbStrategyModuleMcr<>(mCounterexample.getWord().asList(), mPredicateUnifier,
						mEmptyStackFactory, mServices, mLogger, mAbstraction.getAlphabet(),
						createMcrInterpolantProvider());
			default:
				throw new IllegalArgumentException("Setting " + mTaPrefs.interpolantAutomaton() + " is unsupported");
			}
		}

		private IInterpolantProvider<L> createMcrInterpolantProvider() {
			final ManagedScript managedScript = mPrefs.getCfgSmtToolkit().getManagedScript();
			final SimplificationTechnique simplificationTechnique = mPrefs.getSimplificationTechnique();
			switch (mTaPrefs.getMcrInterpolantMethod()) {
			case WP:
				return new WpInterpolantProvider<>(mServices, mLogger, managedScript, simplificationTechnique,
						mPredicateUnifier);
			case SP:
				return new SpInterpolantProvider<>(mServices, mLogger, managedScript, simplificationTechnique,
						mPredicateUnifier);
			default:
				throw new IllegalArgumentException("Setting " + mTaPrefs.getMcrInterpolantMethod() + " is unsupported");
			}
		}

		public IIpAbStrategyModule<L> createIpAbStrategyModuleStraightlineAll() {
			return createInterpolantAutomatonBuilderStrategyModulePreferences(InterpolantAutomaton.STRAIGHT_LINE, null);
		}

		public IIpAbStrategyModule<L> createIpAbStrategyModuleAbstractInterpretation(
				final IpTcStrategyModuleAbstractInterpretation<L> ipTcStrategyModuleAbsInt) {
			return createInterpolantAutomatonBuilderStrategyModulePreferences(
					InterpolantAutomaton.ABSTRACT_INTERPRETATION, null);
		}

		public IIpAbStrategyModule<L> createIpAbStrategyModuleTotalInterpolation() {
			return createInterpolantAutomatonBuilderStrategyModulePreferences(InterpolantAutomaton.TOTALINTERPOLATION,
					null);
		}

		public IIpAbStrategyModule<L> createIpAbStrategyModuleCanonical() {
			return createInterpolantAutomatonBuilderStrategyModulePreferences(InterpolantAutomaton.CANONICAL, null);
		}

		public IIpAbStrategyModule<L> createIpAbStrategyModuleMcr() {
			return createInterpolantAutomatonBuilderStrategyModulePreferences(InterpolantAutomaton.MCR, null);
		}

		public TermClassifier getTermClassifierForTrace() {
			return TraceCheckUtils.classifyTermsInTrace(mCounterexample.getWord(),
					mCfgSmtToolkit.getSmtFunctionsAndAxioms());
		}

		public IPredicateUnifier getDefaultPredicateUnifier() {
			return mPredicateUnifier;
		}

		private void isOnlyDefaultPrePostConditions() {
			if (!SmtUtils.isTrueLiteral(mPrecondition.getFormula())) {
				throw new UnsupportedOperationException("Currently, only precondition true is supported");
			}
			if (!SmtUtils.isFalseLiteral(mPostcondition.getFormula())) {
				throw new UnsupportedOperationException("Currently, only postcondition false is supported");
			}
		}

	}

}
