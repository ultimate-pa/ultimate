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

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Stores predicates for locations of interest (LOIs).
 * Since outsiders may not know whether a location is a LOI or not, the store method
 * {@link #storePredicateIfLoi(IcfgLocation, IPredicate)} takes any location and predicate
 * but updates the predicate only if the given location is of interest.
 * <p>
 * This interface has no way to retrieve the stored predicates.
 * Implementing classes must offer methods to retrieve the stored predicates on their own.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public interface ILoiPredicateStorage {

	/**
	 * Adds a predicate if the given location is of interest.
	 * Whether the added predicate replaces the old one or is combined with the old one depends on the implementation.
	 * Usually we expect that predicates are combined and the initial predicate is bottom/false.
	 *
	 * @param location Location which may be of interest
	 * @param addPred Predicate to be stored in case the location is of interest
	 */
	void storePredicateIfLoi(IcfgLocation location, IPredicate addPred);
}
