package de.uni_freiburg.informatik.ultimate.lib.sifa;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Interface for SIFA interpreters that analyze an ICFG and compute predicates at locations of interest.
 */
public interface ISifaInterpreter {

	/**
	 * Interprets the ICFG starting at the initial nodes.
	 *
	 * @return Map from all locations of interest to invariants (predicates over-approximating the program states at
	 *         these locations)
	 */
	Map<IcfgLocation, IPredicate> interpret();
}
