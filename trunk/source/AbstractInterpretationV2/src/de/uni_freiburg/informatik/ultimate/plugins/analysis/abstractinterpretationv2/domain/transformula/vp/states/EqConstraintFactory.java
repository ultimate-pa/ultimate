package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;

public class EqConstraintFactory<
			ACTION extends IIcfgTransition<IcfgLocation>, NODE extends IEqNodeIdentifier<FUNCTION>, FUNCTION> {

	public EqConstraint<ACTION, NODE, FUNCTION> getEmptyConstraint() {
		return null;
	}

	public EqConstraint<ACTION, NODE, FUNCTION> getBottomConstraint() {
		return null;
	}

	public EqConstraint<ACTION, NODE, FUNCTION> unfreeze(EqConstraint<ACTION, NODE, FUNCTION> constraint) {
		assert constraint.isFrozen();
		// TODO Auto-generated method stub
		return null;
	}

	public EqDisjunctiveConstraint<ACTION, EqNode, IProgramVarOrConst> unfreeze(
			EqDisjunctiveConstraint<ACTION, EqNode, IProgramVarOrConst> constraint) {
		// TODO Auto-generated method stub
		return null;
	}
}
