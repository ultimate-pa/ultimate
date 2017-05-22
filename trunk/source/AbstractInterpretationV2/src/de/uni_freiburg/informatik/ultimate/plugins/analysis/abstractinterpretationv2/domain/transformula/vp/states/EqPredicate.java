package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IAbstractPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;

public class EqPredicate<ACTION extends IIcfgTransition<IcfgLocation>> implements IAbstractPredicate {

	public EqPredicate(EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> constraint) {
		// TODO Auto-generated constructor stub
	}

	@Override
	public String[] getProcedures() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<IProgramVar> getVars() {
		// TODO Auto-generated method stub
		return null;
	}

	public EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> getEqConstraint() {
		// TODO Auto-generated method stub
		return null;
	}

}
