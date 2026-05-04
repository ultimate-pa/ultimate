package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.AbstractLocationPair;
import java.util.Set;

/** Static interference-edge summary prepared once from the ICFG. */
public record TranslatedInterferenceOfEdge(IcfgLocation source, IcfgLocation target, AbstractLocationPair abstractLocationPair,
		IPredicate transitionPredicate, Set<IProgramVar> changedGlobals) {
}
