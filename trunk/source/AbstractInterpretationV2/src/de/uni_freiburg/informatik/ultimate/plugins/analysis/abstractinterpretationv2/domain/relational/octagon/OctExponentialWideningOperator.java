package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;

public class OctExponentialWideningOperator implements IAbstractStateBinaryOperator<OctagonDomainState> {
		
	private final BiFunction<OctMatrix, OctMatrix, OctMatrix> mWideningOperator;
	
	public OctExponentialWideningOperator(OctValue threshold) {
		if (threshold.isInfinity()) {
			throw new IllegalArgumentException("Exponential widening may not reach fixpoint using infinite threshold.");
		}
		mWideningOperator = (m, n) -> m.widenExponential(n, threshold);
	}

	@Override
	public OctagonDomainState apply(OctagonDomainState first, OctagonDomainState second) {
		return first.widen(second, mWideningOperator);
	}
}
