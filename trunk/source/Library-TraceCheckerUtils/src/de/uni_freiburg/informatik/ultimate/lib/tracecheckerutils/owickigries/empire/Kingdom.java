/*
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;

public final class Kingdom<PLACE, LETTER> {
	/**
	 * The set of realms in Kingdom.
	 */
	private final Set<Realm<PLACE, LETTER>> mKingdom;

	public Kingdom(final Set<Realm<PLACE, LETTER>> kingdom) {
		mKingdom = kingdom;
	}

	/**
	 * @return Set of realms in Kingdom.
	 */
	public Set<Realm<PLACE, LETTER>> getRealms() {
		return mKingdom;
	}

	/**
	 * Adds the specified realm into the set of realms in the kingdom.
	 *
	 * @param realm
	 */
	public void addRealm(final Realm<PLACE, LETTER> realm) {
		mKingdom.add(realm);
	}

	/**
	 * Add the specified set of realms into the Kingdom.
	 *
	 * @param realms
	 */
	public void addRealm(final Set<Realm<PLACE, LETTER>> realms) {
		mKingdom.addAll(realms);
	}

	/**
	 * Remove the specified realm from Kingdom.
	 *
	 * @param realm
	 */
	public boolean removeRealm(final Realm<PLACE, LETTER> realm) {
		if (mKingdom.contains(realm)) {
			mKingdom.remove(realm);
			return true;
		}
		return false;
	}

	/**
	 * @param condition
	 * @param bp
	 * @return CoKingdom with corelation type and Kingdom's realms subsets by the corelation type of the realm wrt.
	 *         condition.
	 */
	public CoKingdom<PLACE, LETTER> getCoKingdom(final Condition<LETTER, PLACE> condition,
			final BranchingProcess<LETTER, PLACE> bp) {
		return new CoKingdom<>(this, condition, bp);
	}

}
