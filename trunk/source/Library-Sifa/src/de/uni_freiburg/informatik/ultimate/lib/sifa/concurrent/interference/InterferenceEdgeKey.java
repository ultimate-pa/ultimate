package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

/** Key for a stored interference predicate from one CFG edge. */
public record InterferenceEdgeKey(IcfgLocation source, IcfgLocation target, int predicateIndex) {
}
