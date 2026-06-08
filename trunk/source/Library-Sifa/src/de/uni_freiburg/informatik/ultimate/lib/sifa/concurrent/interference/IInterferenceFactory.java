package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

public interface IInterferenceFactory {
	/**
	 * Builds a single merged interference from the per-location analysis states of all threads.
	 * Keys in perThreadStates are thread IDs; values are their location-state maps.
	 */
	IInterference buildFromAllStates(Map<String, Map<IcfgLocation, IPredicate>> perThreadStates);
}
