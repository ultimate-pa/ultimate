package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;

public interface INonrelationalAbstractState<STATE extends IAbstractState<STATE, ACTION>, ACTION>
        extends IAbstractState<STATE, ACTION> {
	
	public STATE intersect(final STATE other);
}
