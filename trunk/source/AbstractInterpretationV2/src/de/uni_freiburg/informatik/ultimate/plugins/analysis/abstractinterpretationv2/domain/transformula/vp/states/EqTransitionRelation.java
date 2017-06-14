package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ITransitionRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;

public class EqTransitionRelation<ACTION extends IIcfgTransition<IcfgLocation>>  implements ITransitionRelation {
	

	private final TransFormula mTf;
	private final EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> mConstraint;

	public EqTransitionRelation(EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> constraint, TransFormula tf) {
		/* 
		 * an EqTransitionRelation inherits all the ITransitionRelation-properties from the TransFormula it was 
		 * constructed from (see corresponding getters..)
		 */
		mTf = tf;
		
		mConstraint = constraint;
	}

	@Override
	public Set<IProgramVar> getAssignedVars() {
		return mTf.getAssignedVars();
	}

	@Override
	public Map<IProgramVar, TermVariable> getInVars() {
		return mTf.getInVars();
	}

	@Override
	public Map<IProgramVar, TermVariable> getOutVars() {
		return mTf.getOutVars();
	}

	@Override
	public Set<IProgramConst> getNonTheoryConsts() {
		return mTf.getNonTheoryConsts();
	}

	@Override
	public boolean isHavocedOut(IProgramVar bv) {
		return mTf.isHavocedOut(bv);
	}

	@Override
	public boolean isHavocedIn(IProgramVar bv) {
		return mTf.isHavocedIn(bv);
	}

	@Override
	public Set<TermVariable> getAuxVars() {
		return mTf.getAuxVars();
	}

	public EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> getEqConstraint() {
		return mConstraint;
	}
	
	@Override
	public String toString() {
		return "EqTransRel: " + mConstraint.toString();
	}
}
