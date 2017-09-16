package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.initializer;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.PreprocessorAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngineParameters;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IDebugHelper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ILoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.FutureRcfgVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.IcfgAbstractStateStorageProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgDebugHelper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.compound.CompoundDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.compound.CompoundDomainPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.empty.EmptyDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence.CongruenceDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.dataflow.DataflowDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign.SignDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctagonDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctagonDomain.LiteralCollectorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainPreanalysis;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;

public class FixpointEngineParameterFactory {

	private final BoogieSymbolTable mSymbolTable;
	private final IIcfg<?> mRoot;
	private final IUltimateServiceProvider mServices;
	private final LiteralCollectorFactory mLiteralCollector;

	public FixpointEngineParameterFactory(final IIcfg<?> root, final LiteralCollectorFactory literalCollector,
			final IUltimateServiceProvider services) {
		mRoot = root;
		mServices = services;

		final PreprocessorAnnotation pa = PreprocessorAnnotation.getAnnotation(root);
		if (pa == null || pa.getSymbolTable() == null) {
			throw new IllegalArgumentException("Could not get BoogieSymbolTable");
		}
		mSymbolTable = pa.getSymbolTable();
		mLiteralCollector = literalCollector;
	}

	@SuppressWarnings("unchecked")
	public <STATE extends IAbstractState<STATE>>
			FixpointEngineParameters<STATE, IcfgEdge, IProgramVarOrConst, IcfgLocation>
			createParams(final IProgressAwareTimer timer,
					final ITransitionProvider<IcfgEdge, IcfgLocation> transitionProvider,
					final ILoopDetector<IcfgEdge> loopDetector) {
		final IAbstractDomain<STATE, IcfgEdge> domain = (IAbstractDomain<STATE, IcfgEdge>) selectDomain();
		final IAbstractStateStorage<STATE, IcfgEdge, IcfgLocation> storageProvider =
				new IcfgAbstractStateStorageProvider<>(mServices, transitionProvider);

		final IVariableProvider<STATE, IcfgEdge> variableProvider =
				new RcfgVariableProvider<>(mRoot.getCfgSmtToolkit(), mServices);
		final IDebugHelper<STATE, IcfgEdge, IProgramVarOrConst, IcfgLocation> debugHelper =
				new RcfgDebugHelper<>(mRoot.getCfgSmtToolkit(), mServices, mRoot.getCfgSmtToolkit().getSymbolTable());
		return new FixpointEngineParameters<STATE, IcfgEdge, IProgramVarOrConst, IcfgLocation>(mServices,
				IProgramVarOrConst.class).setDomain(domain).setLoopDetector(loopDetector).setStorage(storageProvider)
						.setTransitionProvider(transitionProvider).setVariableProvider(variableProvider)
						.setDebugHelper(debugHelper).setTimer(timer);
	}

	@SuppressWarnings("unchecked")
	public <STATE extends IAbstractState<STATE>>
			FixpointEngineParameters<STATE, IcfgEdge, IProgramVarOrConst, BoogieIcfgLocation>
			createParamsFuture(final IProgressAwareTimer timer,
					final ITransitionProvider<IcfgEdge, BoogieIcfgLocation> transitionProvider,
					final ILoopDetector<IcfgEdge> loopDetector) {
		final IAbstractDomain<STATE, IcfgEdge> domain = (IAbstractDomain<STATE, IcfgEdge>) selectDomainFutureCfg();
		final IAbstractStateStorage<STATE, IcfgEdge, BoogieIcfgLocation> storageProvider =
				new IcfgAbstractStateStorageProvider<>(mServices, transitionProvider);
		final IVariableProvider<STATE, IcfgEdge> variableProvider =
				new FutureRcfgVariableProvider<>(mRoot.getCfgSmtToolkit().getSymbolTable(), mServices);
		final IDebugHelper<STATE, IcfgEdge, IProgramVarOrConst, BoogieIcfgLocation> debugHelper =
				new RcfgDebugHelper<>(mRoot.getCfgSmtToolkit(), mServices, mRoot.getCfgSmtToolkit().getSymbolTable());

		return new FixpointEngineParameters<STATE, IcfgEdge, IProgramVarOrConst, BoogieIcfgLocation>(mServices,
				IProgramVarOrConst.class).setDomain(domain).setLoopDetector(loopDetector).setStorage(storageProvider)
						.setTransitionProvider(transitionProvider).setVariableProvider(variableProvider)
						.setDebugHelper(debugHelper).setTimer(timer);
	}

	/**
	 * Creates parameters for when the equality domain is invoked from another plugin (e.g. HeapSeparator) and should
	 * not take (all) its parameters from the settings.
	 *
	 * @param timer
	 * @param transitionProvider
	 * @param loopDetector
	 * @return
	 */
	@SuppressWarnings("unchecked")
	public <STATE extends IAbstractState<STATE>>
			FixpointEngineParameters<STATE, IcfgEdge, IProgramVarOrConst, BoogieIcfgLocation>
			createParamsFutureEqualityDomain(final IProgressAwareTimer timer,
					final ITransitionProvider<IcfgEdge, BoogieIcfgLocation> transitionProvider,
					final ILoopDetector<IcfgEdge> loopDetector) {
		final ILogger logger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);

		final IAbstractDomain<STATE, IcfgEdge> domain = (IAbstractDomain<STATE, IcfgEdge>) createEqualityDomain(logger);

		final IAbstractStateStorage<STATE, IcfgEdge, BoogieIcfgLocation> storageProvider =
				new IcfgAbstractStateStorageProvider<>(mServices, transitionProvider);

		final IVariableProvider<STATE, IcfgEdge> variableProvider =
				new FutureRcfgVariableProvider<>(mRoot.getCfgSmtToolkit().getSymbolTable(), mServices);

		final IDebugHelper<STATE, IcfgEdge, IProgramVarOrConst, BoogieIcfgLocation> debugHelper =
				new RcfgDebugHelper<>(mRoot.getCfgSmtToolkit(), mServices, mRoot.getCfgSmtToolkit().getSymbolTable());

		return new FixpointEngineParameters<STATE, IcfgEdge, IProgramVarOrConst, BoogieIcfgLocation>(mServices,
				IProgramVarOrConst.class).setDomain(domain).setLoopDetector(loopDetector).setStorage(storageProvider)
						.setTransitionProvider(transitionProvider).setVariableProvider(variableProvider)
						.setDebugHelper(debugHelper).setTimer(timer);
	}

	private IAbstractDomain<?, IcfgEdge> selectDomainFutureCfg() {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final String selectedDomain = prefs.getString(AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN);
		final ILogger logger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);

		if (EmptyDomain.class.getSimpleName().equals(selectedDomain)) {
			return new EmptyDomain<>();
		} else if (DataflowDomain.class.getSimpleName().equals(selectedDomain)) {
			return new DataflowDomain<>(logger);
		} else if (VPDomain.class.getSimpleName().equals(selectedDomain)) {
			return createEqualityDomain(logger);
		}
		throw new UnsupportedOperationException(getFailureString(selectedDomain));
	}

	private IAbstractDomain<?, IcfgEdge> createEqualityDomain(final ILogger logger) {
		final VPDomainPreanalysis preAnalysis = new VPDomainPreanalysis(mRoot, logger, mServices);
		preAnalysis.postProcess();
		// final VPTfStateBuilderPreparer tfPreparer =
		// new VPTfStateBuilderPreparer(preAnalysis, mRoot, logger);
		return new VPDomain<>(logger, mServices, mRoot.getCfgSmtToolkit(), preAnalysis);
	}

	private IAbstractDomain<?, IcfgEdge> selectDomain() {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final String selectedDomain = prefs.getString(AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN);
		final ILogger logger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);

		if (EmptyDomain.class.getSimpleName().equals(selectedDomain)) {
			return new EmptyDomain<>();
		} else if (SignDomain.class.getSimpleName().equals(selectedDomain)) {
			return new SignDomain(mServices, mRoot, mSymbolTable);
		} else if (IntervalDomain.class.getSimpleName().equals(selectedDomain)) {
			return new IntervalDomain(logger, mSymbolTable, mLiteralCollector.create().getLiteralCollection(),
					mServices, mRoot);
		} else if (OctagonDomain.class.getSimpleName().equals(selectedDomain)) {
			return new OctagonDomain(logger, mSymbolTable, mLiteralCollector, mServices, mRoot);
		} else if (CongruenceDomain.class.getSimpleName().equals(selectedDomain)) {
			return new CongruenceDomain(logger, mServices, mSymbolTable, mRoot);
		} else if (CompoundDomain.class.getSimpleName().equals(selectedDomain)) {
			@SuppressWarnings("rawtypes")
			final List<IAbstractDomain> domainList = new ArrayList<>();
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_EMPTY_DOMAIN)) {
				domainList.add(new EmptyDomain<>());
			}
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_SIGN_DOMAIN)) {
				domainList.add(new SignDomain(mServices, mRoot, mSymbolTable));
			}
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_CONGRUENCE_DOMAIN)) {
				domainList.add(new CongruenceDomain(logger, mServices, mSymbolTable, mRoot));
			}
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_INTERVAL_DOMAIN)) {
				domainList.add(new IntervalDomain(logger, mSymbolTable,
						mLiteralCollector.create().getLiteralCollection(), mServices, mRoot));
			}
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_OCTAGON_DOMAIN)) {
				domainList.add(new OctagonDomain(logger, mSymbolTable, mLiteralCollector, mServices, mRoot));
			}
			return new CompoundDomain(mServices, domainList, mRoot);
		}
		throw new UnsupportedOperationException(getFailureString(selectedDomain));
	}

	private static String getFailureString(final String selectedDomain) {
		return "The value \"" + selectedDomain + "\" of preference \"" + AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN
				+ "\" was not considered before! ";
	}
}
