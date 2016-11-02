package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.initializer;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.PreprocessorAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngineParameters;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IDebugHelper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ILoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.DefaultSymbolTableAdapter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.FutureRcfgVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.PathProgramVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgAbstractStateStorageProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgDebugHelper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.compound.CompoundDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.compound.CompoundDomainPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.empty.EmptyDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence.CongruenceDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.dataflow.DataflowDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign.SignDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctagonDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctagonDomain.LiteralCollectorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp.RCFGArrayIndexCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp.VPDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class FixpointEngineParameterFactory {
	
	private final BoogieSymbolTable mSymbolTable;
	private final RootNode mRoot;
	private final IUltimateServiceProvider mServices;
	private final LiteralCollectorFactory mLiteralCollector;
	
	public FixpointEngineParameterFactory(final RootNode root, final LiteralCollectorFactory literalCollector,
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
	public <STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>>
			FixpointEngineParameters<STATE, CodeBlock, IBoogieVar, ProgramPoint, Expression>
			createParams(final IProgressAwareTimer timer,
					final ITransitionProvider<CodeBlock, ProgramPoint> transitionProvider,
					final ILoopDetector<CodeBlock> loopDetector) {
		final RootAnnot rootAnnot = mRoot.getRootAnnot();
		final IAbstractDomain<STATE, CodeBlock, IBoogieVar> domain =
				(IAbstractDomain<STATE, CodeBlock, IBoogieVar>) selectDomain();
		final IAbstractStateStorage<STATE, CodeBlock, IBoogieVar, ProgramPoint> storageProvider =
				new RcfgAbstractStateStorageProvider<>(domain.getMergeOperator(), mServices, transitionProvider);
		
		final IVariableProvider<STATE, CodeBlock, IBoogieVar> variableProvider = new RcfgVariableProvider<>(
				new DefaultSymbolTableAdapter(mSymbolTable, rootAnnot.getBoogie2SMT().getBoogie2SmtSymbolTable()),
				mServices);
		final IDebugHelper<STATE, CodeBlock, IBoogieVar, ProgramPoint> debugHelper =
				new RcfgDebugHelper<>(rootAnnot.getCfgSmtToolkit(), mServices, 
						mRoot.getRootAnnot().getBoogie2SMT().getBoogie2SmtSymbolTable());
		return new FixpointEngineParameters<STATE, CodeBlock, IBoogieVar, ProgramPoint, Expression>(mServices)
				.setDomain(domain).setLoopDetector(loopDetector).setStorage(storageProvider)
				.setTransitionProvider(transitionProvider).setVariableProvider(variableProvider)
				.setDebugHelper(debugHelper).setTimer(timer);
	}
	
	@SuppressWarnings("unchecked")
	public <STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>>
			FixpointEngineParameters<STATE, CodeBlock, IBoogieVar, ProgramPoint, Expression>
			createParamsPathProgram(final IProgressAwareTimer timer,
					final ITransitionProvider<CodeBlock, ProgramPoint> transitionProvider,
					final ILoopDetector<CodeBlock> loopDetector) {
		final RootAnnot rootAnnot = mRoot.getRootAnnot();
		final IAbstractDomain<STATE, CodeBlock, IBoogieVar> domain =
				(IAbstractDomain<STATE, CodeBlock, IBoogieVar>) selectDomain();
		final IAbstractStateStorage<STATE, CodeBlock, IBoogieVar, ProgramPoint> storageProvider =
				new RcfgAbstractStateStorageProvider<>(domain.getMergeOperator(), mServices, transitionProvider);
		final IVariableProvider<STATE, CodeBlock, IBoogieVar> variableProvider = new PathProgramVariableProvider<>(
				new DefaultSymbolTableAdapter(mSymbolTable, rootAnnot.getBoogie2SMT().getBoogie2SmtSymbolTable()),
				mServices);
		final IDebugHelper<STATE, CodeBlock, IBoogieVar, ProgramPoint> debugHelper =
				new RcfgDebugHelper<>(rootAnnot.getCfgSmtToolkit(), mServices, 
						mRoot.getRootAnnot().getBoogie2SMT().getBoogie2SmtSymbolTable());
		return new FixpointEngineParameters<STATE, CodeBlock, IBoogieVar, ProgramPoint, Expression>(mServices)
				.setDomain(domain).setLoopDetector(loopDetector).setStorage(storageProvider)
				.setTransitionProvider(transitionProvider).setVariableProvider(variableProvider)
				.setDebugHelper(debugHelper).setTimer(timer);
	}
	
	@SuppressWarnings("unchecked")
	public <STATE extends IAbstractState<STATE, CodeBlock, IProgramVar>>
			FixpointEngineParameters<STATE, CodeBlock, IProgramVar, ProgramPoint, Expression>
			createParamsFuture(final IProgressAwareTimer timer,
					final ITransitionProvider<CodeBlock, ProgramPoint> transitionProvider,
					final ILoopDetector<CodeBlock> loopDetector) {
		final RootAnnot rootAnnot = mRoot.getRootAnnot();
		
		final IAbstractDomain<STATE, CodeBlock, IProgramVar> domain =
				(IAbstractDomain<STATE, CodeBlock, IProgramVar>) selectDomainFutureCfg();
		final IAbstractStateStorage<STATE, CodeBlock, IProgramVar, ProgramPoint> storageProvider =
				new RcfgAbstractStateStorageProvider<>(domain.getMergeOperator(), mServices, transitionProvider);
		final IVariableProvider<STATE, CodeBlock, IProgramVar> variableProvider = new FutureRcfgVariableProvider<>(
				mSymbolTable, rootAnnot.getBoogie2SMT().getBoogie2SmtSymbolTable(), mServices);
		final IDebugHelper<STATE, CodeBlock, IProgramVar, ProgramPoint> debugHelper =
				new RcfgDebugHelper<>(rootAnnot.getCfgSmtToolkit(), mServices, 
						mRoot.getRootAnnot().getBoogie2SMT().getBoogie2SmtSymbolTable());
		
		return new FixpointEngineParameters<STATE, CodeBlock, IProgramVar, ProgramPoint, Expression>(mServices)
				.setDomain(domain).setLoopDetector(loopDetector).setStorage(storageProvider)
				.setTransitionProvider(transitionProvider).setVariableProvider(variableProvider)
				.setDebugHelper(debugHelper).setTimer(timer);
	}
	
	private IAbstractDomain<?, CodeBlock, IProgramVar> selectDomainFutureCfg() {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final String selectedDomain = prefs.getString(AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN);
		final ILogger logger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		
		if (EmptyDomain.class.getSimpleName().equals(selectedDomain)) {
			return new EmptyDomain<>();
		} else if (DataflowDomain.class.getSimpleName().equals(selectedDomain)) {
			return new DataflowDomain(logger);
		} else if (VPDomain.class.getSimpleName().equals(selectedDomain)) {
			final RCFGArrayIndexCollector arrayIndexCollector = new RCFGArrayIndexCollector(mRoot);
			return new VPDomain(logger, mRoot.getRootAnnot().getCfgSmtToolkit().getManagedScript(), mServices,
					arrayIndexCollector.getEqGraphNodeSet(), arrayIndexCollector.getTermToBaseNodeMap(),
					arrayIndexCollector.getTermToFnNodeMap(), arrayIndexCollector.getEqNodeToEqGraphNodeMap());
		}
		throw new UnsupportedOperationException(getFailureString(selectedDomain));
	}
	
	private IAbstractDomain<?, CodeBlock, IBoogieVar> selectDomain() {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final String selectedDomain = prefs.getString(AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN);
		final ILogger logger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		
		if (EmptyDomain.class.getSimpleName().equals(selectedDomain)) {
			return new EmptyDomain<>();
		} else if (SignDomain.class.getSimpleName().equals(selectedDomain)) {
			return new SignDomain(mServices, mRoot.getRootAnnot(), mSymbolTable);
		} else if (IntervalDomain.class.getSimpleName().equals(selectedDomain)) {
			return new IntervalDomain(logger, mSymbolTable, mLiteralCollector.create().getLiteralCollection(),
					mServices, mRoot.getRootAnnot());
		} else if (OctagonDomain.class.getSimpleName().equals(selectedDomain)) {
			return new OctagonDomain(logger, mSymbolTable, mLiteralCollector, mServices, mRoot.getRootAnnot());
		} else if (CongruenceDomain.class.getSimpleName().equals(selectedDomain)) {
			return new CongruenceDomain(logger, mServices, mSymbolTable, mRoot.getRootAnnot());
		} else if (CompoundDomain.class.getSimpleName().equals(selectedDomain)) {
			@SuppressWarnings("rawtypes")
			final List<IAbstractDomain> domainList = new ArrayList<>();
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_EMPTY_DOMAIN)) {
				domainList.add(new EmptyDomain<>());
			}
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_SIGN_DOMAIN)) {
				domainList.add(new SignDomain(mServices, mRoot.getRootAnnot(), mSymbolTable));
			}
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_CONGRUENCE_DOMAIN)) {
				domainList.add(new CongruenceDomain(logger, mServices, mSymbolTable, mRoot.getRootAnnot()));
			}
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_INTERVAL_DOMAIN)) {
				domainList.add(new IntervalDomain(logger, mSymbolTable,
						mLiteralCollector.create().getLiteralCollection(), mServices, mRoot.getRootAnnot()));
			}
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_OCTAGON_DOMAIN)) {
				domainList.add(
						new OctagonDomain(logger, mSymbolTable, mLiteralCollector, mServices, mRoot.getRootAnnot()));
			}
			return new CompoundDomain(mServices, domainList, mRoot.getRootAnnot());
		}
		throw new UnsupportedOperationException(getFailureString(selectedDomain));
	}
	
	private static String getFailureString(final String selectedDomain) {
		return "The value \"" + selectedDomain + "\" of preference \"" + AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN
				+ "\" was not considered before! ";
	}
}
