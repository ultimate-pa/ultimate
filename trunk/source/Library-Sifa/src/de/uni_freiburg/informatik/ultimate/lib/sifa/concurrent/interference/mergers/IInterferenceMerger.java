package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.mergers;

import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

/**
 * Merges/reduces interferences per thread (e.g., join all into one, limit to N).
 */
public interface IInterferenceMerger {

	InterferenceAbstraction merge(InterferenceAbstraction interferences, IDomain domain);

	static IInterferenceMerger identity() {
		return (interferences, domain) -> interferences;
	}
}
