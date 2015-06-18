package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.access.BaseObserver;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.PreprocessorAnnotation;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ILoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgAbstractStateStorageProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgLoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgTransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.empty.EmptyDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector.RCFGLoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class AbstractInterpretationRcfgObserver extends BaseObserver {

	private final IUltimateServiceProvider mServices;
	private final RCFGLoopDetector mLoopDetector;

	public AbstractInterpretationRcfgObserver(IUltimateServiceProvider services, RCFGLoopDetector loopDetector) {
		mServices = services;
		mLoopDetector = loopDetector;
	}

	@Override
	public boolean process(IElement elem) throws Throwable {
		// TODO: Library mode or main method mode? Currently, we only have main
		// method mode

		if (!(elem instanceof RootNode)) {
			throw new IllegalArgumentException("You cannot use this observer for " + elem.getClass().getSimpleName());
		}
		final RootNode root = (RootNode) elem;

		final BoogieSymbolTable symbolTable = getSymbolTable(root);
		if (symbolTable == null) {
			throw new IllegalArgumentException("Could not get BoogieSymbolTable");
		}

		final List<CodeBlock> initial = getInitialEdges(root);
		if (initial == null) {
			throw new IllegalArgumentException("Could not find initial edge");
		}

		final Boogie2SmtSymbolTable boogieVarTable = root.getRootAnnot().getBoogie2SMT().getBoogie2SmtSymbolTable();

		final IAbstractDomain<CodeBlock, BoogieVar> domain = selectDomain();
		final AbstractInterpreter<CodeBlock, BoogieVar> interpreter = createAbstractInterpreter(domain, symbolTable,
				boogieVarTable);
		interpreter.process(initial);
		return false;
	}

	private BoogieSymbolTable getSymbolTable(RootNode root) {
		final PreprocessorAnnotation pa = PreprocessorAnnotation.getAnnotation(root);
		if (pa == null) {
			return null;
		}
		return pa.getSymbolTable();
	}

	private IAbstractDomain<CodeBlock, BoogieVar> selectDomain() {
		return new EmptyDomain<>();
	}

	private List<CodeBlock> getInitialEdges(RootNode root) {
		for (final RCFGEdge initialEdge : root.getOutgoingEdges()) {
			final ProgramPoint initialNode = (ProgramPoint) initialEdge.getTarget();
			if (initialNode.getProcedure().equals("ULTIMATE.start")) {
				List<RCFGEdge> edges = initialNode.getOutgoingEdges();
				List<CodeBlock> codeblocks = new ArrayList<CodeBlock>(edges.size());
				for (RCFGEdge edge : edges) {
					codeblocks.add((CodeBlock) edge);
				}
				return codeblocks;
			}
		}
		return null;
	}

	private AbstractInterpreter<CodeBlock, BoogieVar> createAbstractInterpreter(
			IAbstractDomain<CodeBlock, BoogieVar> domain, BoogieSymbolTable table, Boogie2SmtSymbolTable boogieVarTable) {
		assert domain != null;
		assert table != null;
		assert boogieVarTable != null;

		ITransitionProvider<CodeBlock> transitionProvider = new RcfgTransitionProvider();
		IAbstractStateStorage<CodeBlock, BoogieVar> storage = new RcfgAbstractStateStorageProvider(
				domain.getMergeOperator());
		IVariableProvider<CodeBlock, BoogieVar> varProvider = new RcfgVariableProvider(table, boogieVarTable);
		ILoopDetector<CodeBlock> loopDetector = new RcfgLoopDetector(mLoopDetector);
		IResultReporter reporter = new RcfgResultReporter();
		return new AbstractInterpreter<CodeBlock, BoogieVar>(mServices, transitionProvider, storage, domain,
				varProvider, loopDetector, reporter);
	}

}
