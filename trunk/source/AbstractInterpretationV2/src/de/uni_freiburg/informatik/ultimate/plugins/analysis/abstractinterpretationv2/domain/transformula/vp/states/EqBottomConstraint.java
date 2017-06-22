package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;

public class EqBottomConstraint<ACTION extends IIcfgTransition<IcfgLocation>, 
		NODE extends IEqNodeIdentifier<NODE, FUNCTION>, 
		FUNCTION extends IEqFunctionIdentifier<NODE, FUNCTION>> 
	extends EqConstraint<ACTION, NODE, FUNCTION> {

	public EqBottomConstraint(EqConstraintFactory<ACTION, NODE, FUNCTION> factory) {
		super(factory);
	}

	@Override
	public boolean isBottom() {
		return true;
	}
}
