package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence;

import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractStateBinaryOperator;

public class CongruenceMergeOperator implements IAbstractStateBinaryOperator<CongruenceDomainState> {
	@Override
	public CongruenceDomainState apply(final CongruenceDomainState first, final CongruenceDomainState second) {
		assert first != null;
		assert second != null;
		
		return first.merge(second);
	}
}
