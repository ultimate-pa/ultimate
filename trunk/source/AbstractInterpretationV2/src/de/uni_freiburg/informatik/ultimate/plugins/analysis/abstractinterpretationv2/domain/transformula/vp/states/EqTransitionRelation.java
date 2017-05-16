package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ITransitionRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;

public class EqTransitionRelation<ACTION extends IIcfgTransition<IcfgLocation>>  implements ITransitionRelation {

	@Override
	public Set<IProgramVar> getAssignedVars() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Map<IProgramVar, TermVariable> getInVars() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Map<IProgramVar, TermVariable> getOutVars() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<IProgramConst> getNonTheoryConsts() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isHavocedOut(IProgramVar bv) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isHavocedIn(IProgramVar bv) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Set<TermVariable> getAuxVars() {
		// TODO Auto-generated method stub
		return null;
	}

	public EqDisjunctiveConstraint<ACTION, EqNode, IProgramVarOrConst> getEqConstraint() {
		// TODO Auto-generated method stub
		return null;
	}

}
