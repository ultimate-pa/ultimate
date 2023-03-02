package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ITermProviderOnDemand;

public interface IAbstractState<STATE extends IAbstractState<STATE>> extends ITermProviderOnDemand {
	STATE join(STATE other);

	STATE widen(STATE other);
}
