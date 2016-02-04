package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;

public class OctExponentialWideningOperator implements IAbstractStateBinaryOperator<OctagonDomainState> {
		
	private final BiFunction<OctMatrix, OctMatrix, OctMatrix> mWideningOperator;
	
	public OctExponentialWideningOperator(BigDecimal threshold) {
		OctValue octThreshold = new OctValue(threshold);
		mWideningOperator = (m, n) -> m.widenExponential(n, octThreshold);
	}

	@Override
	public OctagonDomainState apply(OctagonDomainState first, OctagonDomainState second) {
		return first.widen(second, mWideningOperator);
	}
}
