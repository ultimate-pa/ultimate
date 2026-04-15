package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.AbstractLocationPair;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/** Prepared interference edge paired with the current source state. */
public record InterferenceEdge(PreparedInterferenceEdge prepared, IPredicate sourceState) {

	public IcfgLocation source() {
		return prepared.source();
	}

	public IcfgLocation target() {
		return prepared.target();
	}

	public AbstractLocationPair abstractLocationPair() {
		return prepared.abstractLocationPair();
	}

	public IPredicate transitionPredicate() {
		return prepared.transitionPredicate();
	}

	public Set<TermVariable> modifiedGlobals() {
		return prepared.modifiedGlobals();
	}
}
