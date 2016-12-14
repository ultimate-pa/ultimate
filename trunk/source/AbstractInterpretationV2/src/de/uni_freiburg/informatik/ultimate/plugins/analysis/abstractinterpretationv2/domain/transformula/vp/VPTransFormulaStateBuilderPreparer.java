package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

public class VPTransFormulaStateBuilderPreparer extends RCFGEdgeVisitor {
	
	Map<TransFormula, VPTransitionStateBuilder> mTransFormulaToTransitionStateBuilder = new HashMap<>();
	
	VPDomainPreanalysis mPreAnalysis;

	private final Collection<EqNode> mAllEqNodes;
	private final Set<EqFunctionNode> mAllEqFunctionNodes;
	private final Set<EqNode> mAllEqNonFunctionNodes;
	private final Set<EqNode> mAllConstantEqNodes;
	
	public VPTransFormulaStateBuilderPreparer(VPDomainPreanalysis preAnalysis) {
		mPreAnalysis = preAnalysis;
		
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

	}

	@Override
	protected void visit(CodeBlock c) {
		
		TransFormula tf = c.getTransitionFormula();
		

		VPTransitionStateBuilder vptsb = new VPTransitionStateBuilder(null, mPreAnalysis, tf, mAllConstantEqNodes);
		
		
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
