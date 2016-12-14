package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public class TFEqGraphNode extends EqGraphNode {
	
	

	private final Map<IProgramVar, TermVariable> mInVars;
	private final Map<IProgramVar, TermVariable> mOutVars;
	private final Term mTerm;

	public TFEqGraphNode(EqNode eqNode, 
			Map<IProgramVar, TermVariable> inVars, 
			Map<IProgramVar, TermVariable> outVars,
			Term term) {
		super(eqNode);
		mInVars = inVars;
		mOutVars = outVars;
		mTerm = term;
	}
	
//	void setupTfNode(Map<Term, TFEqGraphNode> termToTfEqGraphNode) {
//		initCcpar = new HashSet<>(this.ccpar);
//		initCcpar = Collections.unmodifiableSet(initCcpar);
//		
//		if (eqNode != null 
//				&& eqNode instanceof EqFunctionNode) {
//			EqFunctionNode eqfn = (EqFunctionNode) eqNode;
//			assert this.ccchild.getImage(eqfn.getFunction()).size() == 1;
//			initCcchild = new ArrayList<>(this.ccchild.getImage(eqfn.getFunction()).iterator().next());
//			initCcchild = Collections.unmodifiableList(initCcchild);
//		}
//	}

}
