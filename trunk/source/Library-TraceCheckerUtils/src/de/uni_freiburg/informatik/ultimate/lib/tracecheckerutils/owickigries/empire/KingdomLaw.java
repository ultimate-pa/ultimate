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

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;

public final class KingdomLaw<PLACE, LETTER> {

	private final Set<Condition<LETTER, PLACE>> mLaw;

	public KingdomLaw(final Set<Condition<LETTER, PLACE>> conditions) {
		mLaw = conditions;
	}

	public void addCondition(final Condition<LETTER, PLACE> condition) {
		mLaw.add(condition);
	}

	public void addCondition(final Set<Condition<LETTER, PLACE>> conditions) {
		mLaw.addAll(conditions);
	}

	public void removeCondition(final Condition<LETTER, PLACE> condition) {
		if (mLaw.contains(condition)) {
			mLaw.remove(condition);
		}
	}

	public Set<Condition<LETTER, PLACE>> getConditions() {
		return mLaw;
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || getClass() != obj.getClass()) {
			return false;
		}
		final KingdomLaw<PLACE, LETTER> other = (KingdomLaw<PLACE, LETTER>) obj;
		return mLaw.equals(other.getConditions());
	}

	@Override
	public int hashCode() {
		return mLaw.hashCode();
	}

}
