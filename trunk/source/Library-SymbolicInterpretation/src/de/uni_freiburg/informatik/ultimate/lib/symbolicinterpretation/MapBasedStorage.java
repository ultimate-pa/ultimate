/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Stores predicates for locations of interest using a map.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class MapBasedStorage implements ILoiPredicateStorage {

	private final IDomain mDomain;
	private final SymbolicTools mTools;
	private final ILogger mLogger;
	private final Map<IcfgLocation, IPredicate> mPredicatesForLoi = new HashMap<>();

	public MapBasedStorage(final Collection<IcfgLocation> locationsOfInterest,
			final IDomain domain, final SymbolicTools tools, final ILogger logger) {
		mDomain = domain;
		mTools = tools;
		mLogger = logger;
		initPredicates(locationsOfInterest);
	}

	private void initPredicates(final Collection<IcfgLocation> locationsOfInterest) {
		final IPredicate bottom = mTools.bottom();
		locationsOfInterest.forEach(loi -> mPredicatesForLoi.put(loi, bottom));
	}

	@Override
	public void storePredicateIfLoi(final IcfgLocation location, final IPredicate addPred) {
		mPredicatesForLoi.computeIfPresent(location,
				(loi, oldPred) -> joinLoiPredicate(loi, oldPred, addPred));
	}

	private IPredicate joinLoiPredicate(final IcfgLocation loi, final IPredicate oldPred, final IPredicate addPred) {
		logBeforeRegisterLoi(loi, addPred);
		final IPredicate newPred = mDomain.join(oldPred, addPred);
		logAfterRegisterLoi(loi, addPred, newPred);
		return newPred;
	}

	// TODO change logging so that we can use this class even when
	// LOIs from this class are different from the user's LOIs, for instance in a ICallSummarizer

	private void logBeforeRegisterLoi(final IcfgLocation loi, final IPredicate addPred) {
		mLogger.debug("LOI %s received the predicate %s", loi, addPred);
	}

	private void logAfterRegisterLoi(final IcfgLocation loi, final IPredicate addedPred, final IPredicate newPred) {
		if (addedPred == newPred) {
			mLogger.debug("Updated predicate for LOI %s is identical", loi);
		} else {
			mLogger.debug("Updated predicate for LOI %s is %s", loi, newPred);
		}
	}

	public Map<IcfgLocation, IPredicate> getMap() {
		return mPredicatesForLoi;
	}
}
