package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

public interface IInterferenceFactory {
	/** Builds an interference from the per-location analysis states of a thread(and its transitions). */
	IInterference buildFromStates(String threadId, Map<IcfgLocation, IPredicate> locationStates);
}
