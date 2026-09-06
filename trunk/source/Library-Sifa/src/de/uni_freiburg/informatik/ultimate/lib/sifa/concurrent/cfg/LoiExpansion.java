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
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public final class LoiExpansion {

	private LoiExpansion() {
	}

	public static Collection<IcfgLocation> getLocationsOfInterestForThread(final String threadId,
			final IIcfg<IcfgLocation> threadIcfg, final Collection<IcfgLocation> requestedLois) {
		final Set<IcfgLocation> filtered = new LinkedHashSet<>();
		if (requestedLois != null) {
			for (final IcfgLocation loi : requestedLois) {
				if (loi != null && containsLocation(threadIcfg, loi)) {
					filtered.add(loi);
				}
			}
		}
		if (!filtered.isEmpty()) {
			return filtered;
		}
		final IcfgLocation entry = threadIcfg.getProcedureEntryNodes().get(threadId);
		if (entry != null) {
			filtered.add(entry);
		}
		final IcfgLocation exit = threadIcfg.getProcedureExitNodes().get(threadId);
		if (exit != null) {
			filtered.add(exit);
		}
		return filtered;
	}

	private static boolean containsLocation(final IIcfg<IcfgLocation> icfg, final IcfgLocation location) {
		return icfg.getProgramPoints().getOrDefault(location.getProcedure(), Map.of()).containsValue(location);
	}
}
