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
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.threadanalysis.fixpoint;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

final class Invariants {
	private final IDomain mDomain;
	private final Set<IcfgLocation> mLocations;
	private Map<IcfgLocation, IPredicate> mRememberedStates = Map.of();

	Invariants(final IDomain domain, final Set<IcfgLocation> locations) {
		mDomain = domain;
		mLocations = locations;
	}

	void rememberCurrentStates(final Map<IcfgLocation, IPredicate> locationInvariants) {
		if (mLocations.isEmpty()) {
			return;
		}
		mRememberedStates = new LinkedHashMap<>(mLocations.size() * 2);
		for (final IcfgLocation location : mLocations) {
			mRememberedStates.put(location, locationInvariants.get(location));
		}
	}

	boolean areUnchanged(final Map<IcfgLocation, IPredicate> locationInvariants) {
		for (final var entry : mRememberedStates.entrySet()) {
			final IPredicate before = entry.getValue();
			final IPredicate after = locationInvariants.get(entry.getKey());
			if (before == after) {
				continue;
			}
			if (before == null || after == null) {
				return false;
			}
			if (!mDomain.isSubsetEq(before, after).isTrueForAbstraction()
					|| !mDomain.isSubsetEq(after, before).isTrueForAbstraction()) {
				return false;
			}
		}
		return true;
	}
}
