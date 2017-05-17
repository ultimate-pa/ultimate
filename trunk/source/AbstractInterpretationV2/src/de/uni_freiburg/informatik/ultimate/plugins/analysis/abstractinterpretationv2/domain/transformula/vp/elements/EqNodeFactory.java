package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class EqNodeFactory {
	
	ManagedScript mMgdScript;

	public EqAtomicBaseNode getOrConstructEqAtomicNode(IProgramVarOrConst varOrConst, Term substitutedTerm) {
		
		return new EqAtomicBaseNode(varOrConst, substitutedTerm, this);
	}

	public EqFunctionNode getOrConstructEqFunctionNode(EqFunction renameVariables, List<EqNode> renamedArgs) {

		final List<Term> paramTerms = renamedArgs.stream().map(eqNode -> eqNode.getTerm()).collect(Collectors.toList());
		mMgdScript.lock(this);
		final Term term = mMgdScript.term(this, 
				EqFunction.getFunctionName(), 
				paramTerms.toArray(new Term[paramTerms.size()]));
		mMgdScript.unlock(this);
		
		
		return  new EqFunctionNode(renameVariables, renamedArgs, term, this);
	}

	public ManagedScript getScript() {
		return mMgdScript;
	}

	public EqNode getOrConstructEqNonAtomicBaseNode(Term substitutedTerm, boolean isGlobal, String procedure) {
		return new EqNonAtomicBaseNode(substitutedTerm, isGlobal, procedure, this);
	}

}
