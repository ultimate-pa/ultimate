package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

public class VPTransFormulaStateBuilderPreparer {
	
	VPDomainPreanalysis mPreAnalysis;

//	private final Collection<EqNode> mAllEqNodes;
//	private final Set<EqFunctionNode> mAllEqFunctionNodes;
//	private final Set<EqNode> mAllEqNonFunctionNodes;
	private final Set<EqNode> mAllConstantEqNodes;
	private final Map<TransFormula, VPTransitionStateBuilder> mTransFormulaToVPTfStateBuilder = 
			new HashMap<>();
	private final ILogger mLogger;
	
	public VPTransFormulaStateBuilderPreparer(VPDomainPreanalysis preAnalysis, IIcfg<?> root, ILogger logger) {
		mPreAnalysis = preAnalysis;
		mLogger = logger;
		
		Collection<EqNode> allEqNodes = preAnalysis.getTermToEqNodeMap().values();
		Set<EqFunctionNode> allEqFunctionNodes = 
				allEqNodes.stream()
				.filter(node -> node instanceof EqFunctionNode)
				.map(node -> (EqFunctionNode) node)
				.collect(Collectors.toSet());
//		HashSet<EqNode> allEqNonFunctionNodes = new HashSet<>(allEqNodes);
		allEqFunctionNodes.removeAll(allEqFunctionNodes);

//		mAllEqNodes = Collections.unmodifiableCollection(allEqNodes);
//		mAllEqFunctionNodes = Collections.unmodifiableSet(allEqFunctionNodes);
//		mAllEqNonFunctionNodes = Collections.unmodifiableSet(allEqNonFunctionNodes);
		
		
		Set<EqNode> allConstantEqNodes = 
				allEqNodes.stream()
				.filter(node -> node.isConstant())
				.collect(Collectors.toSet());
		mAllConstantEqNodes = Collections.unmodifiableSet(allConstantEqNodes);

		process(RcfgUtils.getInitialEdges(root));
	}

	private <T extends IcfgEdge> void process(final Collection<T> edges) {
		mLogger.info("started VPDomainPreAnalysis");
		

		final Deque<IcfgEdge> worklist = new ArrayDeque<>();
		final Set<IcfgEdge> finished = new HashSet<>();

		worklist.addAll(edges);
		while (!worklist.isEmpty()) {
			final IcfgEdge current = worklist.removeFirst();
			if (!finished.add(current)) {
				continue;
			}
			if (current instanceof IAction) {
				visit((IAction) current);
			}
			worklist.addAll(current.getTarget().getOutgoingEdges());
		}
	}
	
	
	protected void visit(IAction c) {
		if (c instanceof ICallAction) {
			visit((ICallAction) c);
		} else if (c instanceof IReturnAction) {
			visit((IReturnAction) c);
		} else if (c instanceof IInternalAction) {
			visit((IInternalAction) c);
		} else {
			assert false : "forgot a case?";
		}
	}
	
	
	protected void visit(ICallAction c) {
		TransFormula tf = c.getLocalVarsAssignment();
		handleTransFormula(tf);
	}

	protected void visit(IReturnAction c) {
		TransFormula tf = c.getAssignmentOfReturn();
		handleTransFormula(tf);
	}

	protected void visit(IInternalAction c) {
		TransFormula tf = c.getTransformula();
		handleTransFormula(tf);
	}



	private void handleTransFormula(TransFormula tf) {
		VPTransitionStateBuilder vptsb = new VPTransitionStateBuilder(mPreAnalysis, tf, mAllConstantEqNodes);
		
		mTransFormulaToVPTfStateBuilder.put(tf, vptsb);
	}
	
	
	VPTransitionStateBuilder getVPTfStateBuilder(TransFormula tf) {
		VPTransitionStateBuilder result = mTransFormulaToVPTfStateBuilder.get(tf);
		assert result != null : "we should have a VPTransitionStateBuidler for every Transformula in the program";
		assert result.isTopConsistent();
		return result;
	}

	public Set<EqNode> getAllConstantEqNodes() {
		return mAllConstantEqNodes;
	}
}
