package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.explicit;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.generic.LiteralCollection;

public class ExplicitValueWideningOperator implements IAbstractStateBinaryOperator<ExplicitValueState> {

	public ExplicitValueWideningOperator(final LiteralCollection mLiteralCollection) {
		// not necessary
	}

	@Override
	public ExplicitValueState apply(final ExplicitValueState first, final ExplicitValueState second) {
		return first.union(second);
	}

}
