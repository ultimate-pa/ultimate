package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.AbstractMultiState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;

public class EqDisjunctiveConstraint<
				ACTION extends IIcfgTransition<IcfgLocation>, NODE extends IEqNodeIdentifier<FUNCTION>, FUNCTION> 
     			 	extends AbstractMultiState<EqConstraint<ACTION, NODE, FUNCTION>, IProgramVarOrConst>{

	Set<EqConstraint<ACTION, NODE, FUNCTION>> mConstraints;

	public boolean isBottom() {
		// TODO Auto-generated method stub
		return false;
	}

	public void renameVariables(Map<Term, Term> substitutionMapping) {
		// TODO Auto-generated method stub
		
	}

	public void freeze() {
		// TODO Auto-generated method stub
		
	}

	public void projectExistentially(Set<TermVariable> varsToProjectAway) {
		// TODO Auto-generated method stub
		
	}
}
