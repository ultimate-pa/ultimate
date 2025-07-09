package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public record Interference<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>(
		ACTION action, GuardedInterferenceDomainState<STATE, ACTION, LOC> preState) {
	boolean isEqualTo(final Interference<STATE, ACTION, LOC> other) {
		return preState().isEqualTo(other.preState());
	}
}
