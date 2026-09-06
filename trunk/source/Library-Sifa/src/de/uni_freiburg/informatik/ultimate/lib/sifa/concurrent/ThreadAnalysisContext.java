/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
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
