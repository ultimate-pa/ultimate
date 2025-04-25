package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class GuardedStateUnionOperator<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>
		implements IAbstractStateBinaryOperator<GuardedInterferenceDomainState<STATE, ACTION, LOC>> {

	@Override
	public GuardedInterferenceDomainState<STATE, ACTION, LOC> apply(
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> first,
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> second) {
		return first.union(second);
	}

}
