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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngineParameters;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IDebugHelper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ILoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.DefaultSymbolTableAdapter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.FutureRcfgVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.IcfgAbstractStateStorageProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.PathProgramVariableProvider;
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
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPTransFormulaStateBuilderPreparer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

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
	public <STATE extends IAbstractState<STATE, IBoogieVar>>
			FixpointEngineParameters<STATE, CodeBlock, IBoogieVar, IcfgLocation>
			createParams(final IProgressAwareTimer timer,
					final ITransitionProvider<CodeBlock, IcfgLocation> transitionProvider,
					final ILoopDetector<CodeBlock> loopDetector) {
		final IAbstractDomain<STATE, CodeBlock, IBoogieVar> domain =
				(IAbstractDomain<STATE, CodeBlock, IBoogieVar>) selectDomain();
		final IAbstractStateStorage<STATE, CodeBlock, IBoogieVar, IcfgLocation> storageProvider =
				new IcfgAbstractStateStorageProvider<>(domain.getMergeOperator(), mServices, transitionProvider);

		final IVariableProvider<STATE, CodeBlock, IBoogieVar> variableProvider = new RcfgVariableProvider<>(
				new DefaultSymbolTableAdapter(mSymbolTable, mRoot.getCfgSmtToolkit().getSymbolTable()), mServices);
		final IDebugHelper<STATE, CodeBlock, IBoogieVar, IcfgLocation> debugHelper =
				new RcfgDebugHelper<>(mRoot.getCfgSmtToolkit(), mServices, mRoot.getCfgSmtToolkit().getSymbolTable());
		return new FixpointEngineParameters<STATE, CodeBlock, IBoogieVar, IcfgLocation>(mServices, IBoogieVar.class)
				.setDomain(domain).setLoopDetector(loopDetector).setStorage(storageProvider)
				.setTransitionProvider(transitionProvider).setVariableProvider(variableProvider)
				.setDebugHelper(debugHelper).setTimer(timer);
	}

	@SuppressWarnings("unchecked")
	public <STATE extends IAbstractState<STATE, IBoogieVar>>
			FixpointEngineParameters<STATE, CodeBlock, IBoogieVar, IcfgLocation>
			createParamsPathProgram(final IProgressAwareTimer timer,
					final ITransitionProvider<CodeBlock, IcfgLocation> transitionProvider,
					final ILoopDetector<CodeBlock> loopDetector) {
		final IAbstractDomain<STATE, CodeBlock, IBoogieVar> domain =
				(IAbstractDomain<STATE, CodeBlock, IBoogieVar>) selectDomain();
		final IAbstractStateStorage<STATE, CodeBlock, IBoogieVar, IcfgLocation> storageProvider =
				new IcfgAbstractStateStorageProvider<>(domain.getMergeOperator(), mServices, transitionProvider);
		final IVariableProvider<STATE, CodeBlock, IBoogieVar> variableProvider = new PathProgramVariableProvider<>(
				new DefaultSymbolTableAdapter(mSymbolTable, mRoot.getCfgSmtToolkit().getSymbolTable()), mServices);
		final IDebugHelper<STATE, CodeBlock, IBoogieVar, IcfgLocation> debugHelper =
				new RcfgDebugHelper<>(mRoot.getCfgSmtToolkit(), mServices, mRoot.getCfgSmtToolkit().getSymbolTable());
		return new FixpointEngineParameters<STATE, CodeBlock, IBoogieVar, IcfgLocation>(mServices, IBoogieVar.class)
				.setDomain(domain).setLoopDetector(loopDetector).setStorage(storageProvider)
				.setTransitionProvider(transitionProvider).setVariableProvider(variableProvider)
				.setDebugHelper(debugHelper).setTimer(timer);
	}

	@SuppressWarnings("unchecked")
	public <STATE extends IAbstractState<STATE, IProgramVarOrConst>>
			FixpointEngineParameters<STATE, CodeBlock, IProgramVarOrConst, BoogieIcfgLocation>
			createParamsFuture(final IProgressAwareTimer timer,
					final ITransitionProvider<CodeBlock, BoogieIcfgLocation> transitionProvider,
					final ILoopDetector<CodeBlock> loopDetector) {
		final IAbstractDomain<STATE, CodeBlock, IProgramVarOrConst> domain =
				(IAbstractDomain<STATE, CodeBlock, IProgramVarOrConst>) selectDomainFutureCfg();
		final IAbstractStateStorage<STATE, CodeBlock, IProgramVarOrConst, BoogieIcfgLocation> storageProvider =
				new IcfgAbstractStateStorageProvider<>(domain.getMergeOperator(), mServices, transitionProvider);
		final IVariableProvider<STATE, CodeBlock, IProgramVarOrConst> variableProvider =
				new FutureRcfgVariableProvider<>(mRoot.getCfgSmtToolkit().getSymbolTable(), mServices);
		final IDebugHelper<STATE, CodeBlock, IProgramVarOrConst, BoogieIcfgLocation> debugHelper =
				new RcfgDebugHelper<>(mRoot.getCfgSmtToolkit(), mServices, mRoot.getCfgSmtToolkit().getSymbolTable());

		return new FixpointEngineParameters<STATE, CodeBlock, IProgramVarOrConst, BoogieIcfgLocation>(mServices,
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
	public <STATE extends IAbstractState<STATE, IProgramVarOrConst>>
			FixpointEngineParameters<STATE, CodeBlock, IProgramVarOrConst, BoogieIcfgLocation>
			createParamsFutureEqualityDomain(final IProgressAwareTimer timer,
					final ITransitionProvider<CodeBlock, BoogieIcfgLocation> transitionProvider,
					final ILoopDetector<CodeBlock> loopDetector) {
		final ILogger logger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);

		final IAbstractDomain<STATE, CodeBlock, IProgramVarOrConst> domain =
				(IAbstractDomain<STATE, CodeBlock, IProgramVarOrConst>) createEqualityDomain(logger);

		final IAbstractStateStorage<STATE, CodeBlock, IProgramVarOrConst, BoogieIcfgLocation> storageProvider =
				new IcfgAbstractStateStorageProvider<>(domain.getMergeOperator(), mServices, transitionProvider);

		final IVariableProvider<STATE, CodeBlock, IProgramVarOrConst> variableProvider =
				new FutureRcfgVariableProvider<>(mRoot.getCfgSmtToolkit().getSymbolTable(), mServices);

		final IDebugHelper<STATE, CodeBlock, IProgramVarOrConst, BoogieIcfgLocation> debugHelper =
				new RcfgDebugHelper<>(mRoot.getCfgSmtToolkit(), mServices, mRoot.getCfgSmtToolkit().getSymbolTable());

		return new FixpointEngineParameters<STATE, CodeBlock, IProgramVarOrConst, BoogieIcfgLocation>(mServices,
				IProgramVarOrConst.class).setDomain(domain).setLoopDetector(loopDetector).setStorage(storageProvider)
						.setTransitionProvider(transitionProvider).setVariableProvider(variableProvider)
						.setDebugHelper(debugHelper).setTimer(timer);
	}

	private IAbstractDomain<?, CodeBlock, IProgramVarOrConst> selectDomainFutureCfg() {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final String selectedDomain = prefs.getString(AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN);
		final ILogger logger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);

		if (EmptyDomain.class.getSimpleName().equals(selectedDomain)) {
			return new EmptyDomain<>(IProgramVarOrConst.class);
		} else if (DataflowDomain.class.getSimpleName().equals(selectedDomain)) {
			return new DataflowDomain<>(logger);
		} else if (VPDomain.class.getSimpleName().equals(selectedDomain)) {
			return createEqualityDomain(logger);
		}
		throw new UnsupportedOperationException(getFailureString(selectedDomain));
	}

	private IAbstractDomain<?, CodeBlock, IProgramVarOrConst> createEqualityDomain(final ILogger logger) {
		final VPDomainPreanalysis preAnalysis = new VPDomainPreanalysis(mRoot, logger);
		preAnalysis.postProcess();
		final VPTransFormulaStateBuilderPreparer tfPreparer =
				new VPTransFormulaStateBuilderPreparer(preAnalysis, mRoot, logger);
		return new VPDomain<>(logger, mRoot.getCfgSmtToolkit().getManagedScript(), mServices,
				mRoot.getCfgSmtToolkit().getSymbolTable(), preAnalysis, tfPreparer);
	}

	private IAbstractDomain<?, CodeBlock, IBoogieVar> selectDomain() {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final String selectedDomain = prefs.getString(AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN);
		final ILogger logger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);

		if (EmptyDomain.class.getSimpleName().equals(selectedDomain)) {
			return new EmptyDomain<>(IBoogieVar.class);
		} else if (SignDomain.class.getSimpleName().equals(selectedDomain)) {
			return new SignDomain(mServices, (IIcfg<BoogieIcfgLocation>) mRoot, mSymbolTable);
		} else if (IntervalDomain.class.getSimpleName().equals(selectedDomain)) {
			return new IntervalDomain(logger, mSymbolTable, mLiteralCollector.create().getLiteralCollection(),
					mServices, (BoogieIcfgContainer) mRoot);
		} else if (OctagonDomain.class.getSimpleName().equals(selectedDomain)) {
			return new OctagonDomain(logger, mSymbolTable, mLiteralCollector, mServices, (BoogieIcfgContainer) mRoot);
		} else if (CongruenceDomain.class.getSimpleName().equals(selectedDomain)) {
			return new CongruenceDomain(logger, mServices, mSymbolTable, (BoogieIcfgContainer) mRoot);
		} else if (CompoundDomain.class.getSimpleName().equals(selectedDomain)) {
			@SuppressWarnings("rawtypes")
			final List<IAbstractDomain> domainList = new ArrayList<>();
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_EMPTY_DOMAIN)) {
				domainList.add(new EmptyDomain<>(IBoogieVar.class));
			}
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_SIGN_DOMAIN)) {
				domainList.add(new SignDomain(mServices, (IIcfg<BoogieIcfgLocation>) mRoot, mSymbolTable));
			}
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_CONGRUENCE_DOMAIN)) {
				domainList.add(new CongruenceDomain(logger, mServices, mSymbolTable, (BoogieIcfgContainer) mRoot));
			}
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_INTERVAL_DOMAIN)) {
				domainList.add(new IntervalDomain(logger, mSymbolTable,
						mLiteralCollector.create().getLiteralCollection(), mServices, (BoogieIcfgContainer) mRoot));
			}
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_OCTAGON_DOMAIN)) {
				domainList.add(new OctagonDomain(logger, mSymbolTable, mLiteralCollector, mServices,
						(BoogieIcfgContainer) mRoot));
			}
			return new CompoundDomain(mServices, domainList, (BoogieIcfgContainer) mRoot);
		}
		throw new UnsupportedOperationException(getFailureString(selectedDomain));
	}

	private static String getFailureString(final String selectedDomain) {
		return "The value \"" + selectedDomain + "\" of preference \"" + AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN
				+ "\" was not considered before! ";
	}
}
