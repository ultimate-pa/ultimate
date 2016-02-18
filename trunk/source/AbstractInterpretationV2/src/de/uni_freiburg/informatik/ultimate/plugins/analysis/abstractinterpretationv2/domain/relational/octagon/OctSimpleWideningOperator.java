package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;

public class OctSimpleWideningOperator implements IAbstractStateBinaryOperator<OctDomainState> {

	@Override
	public OctDomainState apply(OctDomainState first, OctDomainState second) {
		return first.widen(second, OctMatrix::widenSimple);
	}

}
