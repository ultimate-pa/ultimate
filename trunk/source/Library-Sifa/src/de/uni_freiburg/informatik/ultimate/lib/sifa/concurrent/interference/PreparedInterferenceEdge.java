package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.AbstractLocationPair;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/** Static interference-edge summary prepared once from the ICFG. */
public record PreparedInterferenceEdge(IcfgLocation source, IcfgLocation target, AbstractLocationPair abstractLocationPair,
		IPredicate transitionPredicate, Set<TermVariable> modifiedGlobals) {
}
