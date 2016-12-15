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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
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

public class VPTransFormulaStateBuilderPreparer extends RCFGEdgeVisitor {
	
	Map<TransFormula, VPTransitionStateBuilder> mTransFormulaToTransitionStateBuilder = new HashMap<>();
	
	VPDomainPreanalysis mPreAnalysis;

	private final Collection<EqNode> mAllEqNodes;
	private final Set<EqFunctionNode> mAllEqFunctionNodes;
	private final Set<EqNode> mAllEqNonFunctionNodes;
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
		HashSet<EqNode> allEqNonFunctionNodes = new HashSet<>(allEqNodes);
		allEqFunctionNodes.removeAll(allEqFunctionNodes);

		mAllEqNodes = Collections.unmodifiableCollection(allEqNodes);
		mAllEqFunctionNodes = Collections.unmodifiableSet(allEqFunctionNodes);
		mAllEqNonFunctionNodes = Collections.unmodifiableSet(allEqNonFunctionNodes);
		
		
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
			visit(current);
			worklist.addAll(current.getTarget().getOutgoingEdges());
		}
	}
	
	// TODO: move to interfaces I<X>Action, the visitor is unnecessary, then
	
	@Override
	protected void visit(CodeBlock c) {
		TransFormula tf = c.getTransitionFormula();
		handleTransFormula(tf);
	}


	private void handleTransFormula(TransFormula tf) {
		VPTransitionStateBuilder vptsb = new VPTransitionStateBuilder(null, mPreAnalysis, tf, mAllConstantEqNodes);
		
		mTransFormulaToVPTfStateBuilder.put(tf, vptsb);
	}
	
	
	VPTransitionStateBuilder getVPTfStateBuilder(TransFormula tf) {
		VPTransitionStateBuilder result = mTransFormulaToTransitionStateBuilder.get(tf);
		assert result != null : "we should have a VPTransitionStateBuidler for every Transformula in the program";
		return result;
	}

}

class TrackedTermFinder extends TermTransformer {

	@Override
	protected void convert(Term term) {
		// TODO Auto-generated method stub
		super.convert(term);
	}

	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
		// TODO Auto-generated method stub
		super.convertApplicationTerm(appTerm, newArgs);
	}
	
}
