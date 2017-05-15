package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;

public class EqConstraintFactory<NODE extends IEqNodeIdentifier<FUNCTION>, FUNCTION> {

	public EqConstraint<NODE, FUNCTION> getEmptyConstraint() {
		return null;
	}

	public EqConstraint<NODE, FUNCTION> getBottomConstraint() {
		return null;
	}

	public EqConstraint<NODE, FUNCTION> unfreeze(EqConstraint<NODE, FUNCTION> constraint) {
		assert constraint.isFrozen();
		// TODO Auto-generated method stub
		return null;
	}

	public EqDisjunctiveConstraint<EqNode, IProgramVarOrConst> unfreeze(
			EqDisjunctiveConstraint<EqNode, IProgramVarOrConst> constraint) {
		// TODO Auto-generated method stub
		return null;
	}
}
