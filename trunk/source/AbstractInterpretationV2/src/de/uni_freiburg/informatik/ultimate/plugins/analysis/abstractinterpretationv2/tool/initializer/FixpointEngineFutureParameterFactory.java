package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.initializer;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngineParameters;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IDebugHelper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ILoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.FutureRcfgVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.IcfgAbstractStateStorageProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgDebugHelper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.empty.EmptyDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.dataflow.DataflowDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainPreanalysis;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPTransFormulaStateBuilderPreparer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;

public class FixpointEngineFutureParameterFactory {
	
	private final IIcfg<?> mRoot;
	private final IUltimateServiceProvider mServices;

	public FixpointEngineFutureParameterFactory(final IIcfg<?> root, final IUltimateServiceProvider services) {
		mRoot = root;
		mServices = services;
	}

	@SuppressWarnings("unchecked")
	public <STATE extends IAbstractState<STATE, IProgramVar>>
			FixpointEngineParameters<STATE, IcfgEdge, IProgramVar, IcfgLocation, Expression>
			createParamsFuture(final IProgressAwareTimer timer,
					final ITransitionProvider<IcfgEdge, IcfgLocation> transitionProvider,
					final ILoopDetector<IcfgEdge> loopDetector) {
		final IAbstractDomain<STATE, IcfgEdge, IProgramVar> domain =
				(IAbstractDomain<STATE, IcfgEdge, IProgramVar>) selectDomainFutureCfg();
		final IAbstractStateStorage<STATE, IcfgEdge, IProgramVar, IcfgLocation> storageProvider =
				new IcfgAbstractStateStorageProvider<>(domain.getMergeOperator(), mServices, transitionProvider);
		final IVariableProvider<STATE, IcfgEdge, IProgramVar> variableProvider =
				new FutureRcfgVariableProvider<>(mRoot.getSymboltable(), mServices);
		final IDebugHelper<STATE, IcfgEdge, IProgramVar, IcfgLocation> debugHelper =
				new RcfgDebugHelper<>(mRoot.getCfgSmtToolkit(), mServices, mRoot.getSymboltable());

		return new FixpointEngineParameters<STATE, IcfgEdge, IProgramVar, IcfgLocation, Expression>(mServices)
				.setDomain(domain).setLoopDetector(loopDetector).setStorage(storageProvider)
				.setTransitionProvider(transitionProvider).setVariableProvider(variableProvider)
				.setDebugHelper(debugHelper).setTimer(timer);
	}

	public <STATE extends IAbstractState<STATE, IProgramVar>>
			FixpointEngineParameters<STATE, IcfgEdge, IProgramVar, IcfgLocation, Expression>
			createParamsFuture(final IProgressAwareTimer timer,
					final ITransitionProvider<IcfgEdge, IcfgLocation> transitionProvider,
					final ILoopDetector<IcfgEdge> loopDetector,
					final IAbstractDomain<STATE, IcfgEdge, IProgramVar> domain) {
		final IAbstractStateStorage<STATE, IcfgEdge, IProgramVar, IcfgLocation> storageProvider =
				new IcfgAbstractStateStorageProvider<>(domain.getMergeOperator(), mServices, transitionProvider);
		final IVariableProvider<STATE, IcfgEdge, IProgramVar> variableProvider =
				new FutureRcfgVariableProvider<>(mRoot.getSymboltable(), mServices);
		final IDebugHelper<STATE, IcfgEdge, IProgramVar, IcfgLocation> debugHelper =
				new RcfgDebugHelper<>(mRoot.getCfgSmtToolkit(), mServices, mRoot.getSymboltable());
		return new FixpointEngineParameters<STATE, IcfgEdge, IProgramVar, IcfgLocation, Expression>(mServices)
				.setDomain(domain).setLoopDetector(loopDetector).setStorage(storageProvider)
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
	public <STATE extends IAbstractState<STATE, IProgramVar>>
			FixpointEngineParameters<STATE, IcfgEdge, IProgramVar, IcfgLocation, Expression>
			createParamsFutureEqualityDomain(final IProgressAwareTimer timer,
					final ITransitionProvider<IcfgEdge, IcfgLocation> transitionProvider,
					final ILoopDetector<IcfgEdge> loopDetector) {
		final ILogger logger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		final IAbstractDomain<STATE, IcfgEdge, IProgramVar> domain =
				(IAbstractDomain<STATE, IcfgEdge, IProgramVar>) createEqualityDomain(logger);
		final IAbstractStateStorage<STATE, IcfgEdge, IProgramVar, IcfgLocation> storageProvider =
				new IcfgAbstractStateStorageProvider<>(domain.getMergeOperator(), mServices, transitionProvider);
		final IVariableProvider<STATE, IcfgEdge, IProgramVar> variableProvider =
				new FutureRcfgVariableProvider<>(mRoot.getSymboltable(), mServices);
		final IDebugHelper<STATE, IcfgEdge, IProgramVar, IcfgLocation> debugHelper =
				new RcfgDebugHelper<>(mRoot.getCfgSmtToolkit(), mServices, mRoot.getSymboltable());
		return new FixpointEngineParameters<STATE, IcfgEdge, IProgramVar, IcfgLocation, Expression>(mServices)
				.setDomain(domain).setLoopDetector(loopDetector).setStorage(storageProvider)
				.setTransitionProvider(transitionProvider).setVariableProvider(variableProvider)
				.setDebugHelper(debugHelper).setTimer(timer);
	}

	public <STATE extends IAbstractState<STATE, IProgramVar>> IAbstractDomain<STATE, IcfgEdge, IProgramVar>
			selectDomainFutureCfg() {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final String selectedDomain = prefs.getString(AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN);
		final ILogger logger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		return selectDomainFutureCfg(selectedDomain, logger);
	}

	@SuppressWarnings("unchecked")
	private <STATE extends IAbstractState<STATE, IProgramVar>> IAbstractDomain<STATE, IcfgEdge, IProgramVar>
			selectDomainFutureCfg(final String domainName, final ILogger logger) {
		if (EmptyDomain.class.getSimpleName().equals(domainName)) {
			return (IAbstractDomain<STATE, IcfgEdge, IProgramVar>) new EmptyDomain<IcfgEdge, IProgramVar>();
		} else if (DataflowDomain.class.getSimpleName().equals(domainName)) {
			return (IAbstractDomain<STATE, IcfgEdge, IProgramVar>) new DataflowDomain<IcfgEdge>(logger);
		} else if (VPDomain.class.getSimpleName().equals(domainName)) {
			return (IAbstractDomain<STATE, IcfgEdge, IProgramVar>) createEqualityDomain(logger);
		}
		throw new UnsupportedOperationException(getFailureString(domainName));
	}

	public <DOM extends IAbstractDomain<STATE, IcfgEdge, IProgramVar>, STATE extends IAbstractState<STATE, IProgramVar>>
			IAbstractDomain<STATE, IcfgEdge, IProgramVar>
			selectDomainFutureCfg(final Class<DOM> domain, final ILogger logger) {
		return selectDomainFutureCfg(Objects.requireNonNull(domain).getSimpleName(), logger);
	}

	public IAbstractDomain<VPState<IcfgEdge>, IcfgEdge, IProgramVar> createEqualityDomain(final ILogger logger) {
		final VPDomainPreanalysis preAnalysis = new VPDomainPreanalysis(mRoot, logger);
		preAnalysis.postProcess();
		final VPTransFormulaStateBuilderPreparer tfPreparer =
				new VPTransFormulaStateBuilderPreparer(preAnalysis, mRoot, logger);
		return new VPDomain<>(logger, mRoot.getCfgSmtToolkit().getManagedScript(), mServices, mRoot.getSymboltable(),
				preAnalysis, tfPreparer);
	}

	private static String getFailureString(final String selectedDomain) {
		return "The value \"" + selectedDomain + "\" of preference \"" + AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN
				+ "\" was not considered before! ";
	}
}
