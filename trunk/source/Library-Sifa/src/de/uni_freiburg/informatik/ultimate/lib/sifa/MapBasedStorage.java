/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.lib.sifa;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Stores predicates for locations of interest using a map.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class MapBasedStorage implements ILoiPredicateStorage {

	private final ILogger mLogger;
	private final Map<IcfgLocation, IPredicate> mPredsForLocs = new HashMap<>();

	public MapBasedStorage(final ILogger logger) {
		mLogger = logger;
	}

	@Override
	public void storePredicate(final IcfgLocation location, final IPredicate addPred) {
		logBeforeRegisterLoi(location, addPred);
		final IPredicate oldPred = mPredsForLocs.put(location, addPred);
		if (oldPred != null) {
			// our iteration order should guarantee that each LOI only receives a predicate at most once
			// see Claus Schaetzle's master's thesis
			throw new IllegalStateException("Tried to register predicate for LOI which already had a predicate.");
		}
	}

	// TODO change logging so that we can use this class even when
	// LOIs from this class are different from the user's LOIs, for instance in a ICallSummarizer
	private void logBeforeRegisterLoi(final IcfgLocation loi, final IPredicate addPred) {
		mLogger.debug("LOI %s received the predicate %s", loi, addPred);
	}

	public Map<IcfgLocation, IPredicate> getMap() {
		return mPredsForLocs;
	}

	public Map<IcfgLocation, IPredicate> addDefaultsAndGetMap(
			final Collection<IcfgLocation> locations, final IPredicate defaultPred) {
		locations.forEach(loc -> mPredsForLocs.putIfAbsent(loc, defaultPred));
		return mPredsForLocs;
	}

	public IPredicate getSingletonOrDefault(final IPredicate defaultPred) {
		if (mPredsForLocs.isEmpty()) {
			return defaultPred;
		} else if (mPredsForLocs.size() == 1) {
			return mPredsForLocs.values().iterator().next();
		} else {
			throw new IllegalStateException("Excepted single value but found " + mPredsForLocs);
		}
	}
}
