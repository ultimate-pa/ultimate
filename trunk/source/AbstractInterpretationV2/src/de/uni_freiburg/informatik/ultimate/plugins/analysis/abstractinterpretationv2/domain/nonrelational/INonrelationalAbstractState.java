package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;

public interface INonrelationalAbstractState<STATE extends IAbstractState<STATE, ACTION, IBoogieVar>, ACTION>
		extends IAbstractState<STATE, ACTION, IBoogieVar> {

	STATE intersect(final STATE other);
}
