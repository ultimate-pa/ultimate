package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceSet;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadActivityPreanalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

record ThreadAnalysisContext(String threadId, IInterferenceSet interference, IDomain domain,
		boolean includeSelfInterference, List<String> sortedInterferenceThreadIds,
		Map<IcfgLocation, IPredicate> locationPredicates,
		Map<IcfgLocation, Set<String>> activeThreadIdsByLocation) {

	Set<String> activeInterferenceThreadsAt(final IcfgLocation location,
			final ThreadActivityPreanalysis preanalysis) {
		return activeThreadIdsByLocation.computeIfAbsent(location,
				loc -> computeActiveInterferenceThreads(loc, preanalysis));
	}

	private Set<String> computeActiveInterferenceThreads(final IcfgLocation location,
			final ThreadActivityPreanalysis preanalysis) {
		final Set<String> result = new LinkedHashSet<>();
		for (final String otherId : sortedInterferenceThreadIds) {
			if (otherId.equals(threadId) && !includeSelfInterference) {
				continue;
			}
			if (!preanalysis.mayBeActiveAt(location, otherId)) {
				continue;
			}
			if (preanalysis.isDefinitelyJoinedAt(location, otherId)) {
				continue;
			}
			result.add(otherId);
		}
		return Set.copyOf(result);
	}
}
