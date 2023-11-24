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

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;

/**
 * Class Law implements a set of corelated assertion Conditions. Law is immutable.
 *
 * @author Matthias Zumkeller (zumkellm@informatik.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 * @param <LETTER>
 *            The type of statements in the Petri program
 */
public final class KingdomLaw<PLACE, LETTER> {

	private final Set<Condition<LETTER, PLACE>> mLaw;

	public KingdomLaw(final Set<Condition<LETTER, PLACE>> conditions) {
		mLaw = new HashSet<>(conditions);
	}

	/**
	 * Add Condition to law and return new Law containing it.
	 *
	 * @param condition
	 *            Condition to be added
	 * @return New Law with added condition.
	 */
	public KingdomLaw<PLACE, LETTER> addCondition(final Condition<LETTER, PLACE> condition) {
		final Set<Condition<LETTER, PLACE>> lawConditions = getConditions();
		lawConditions.add(condition);
		return new KingdomLaw<>(lawConditions);
	}

	/**
	 * Add Conditions to law and return new Law containing it.
	 *
	 * @param conditions
	 *            Conditions to be added
	 * @return New Law with added conditions.
	 */
	public KingdomLaw<PLACE, LETTER> addCondition(final Set<Condition<LETTER, PLACE>> conditions) {
		final Set<Condition<LETTER, PLACE>> lawConditions = getConditions();
		lawConditions.addAll(conditions);
		return new KingdomLaw<>(lawConditions);
	}

	/**
	 * Remove condition and return new Law without it.
	 *
	 * @param condition
	 *            Condition to be removed
	 * @return New Law without condition.
	 */
	public KingdomLaw<PLACE, LETTER> removeCondition(final Condition<LETTER, PLACE> condition) {
		if (mLaw.contains(condition)) {
			final Set<Condition<LETTER, PLACE>> lawConditions = getConditions();
			lawConditions.remove(condition);
			return new KingdomLaw<>(lawConditions);
		}
		return new KingdomLaw<>(mLaw);
	}

	public Set<Condition<LETTER, PLACE>> getConditions() {
		return new HashSet<>(mLaw);
	}

	/**
	 * Assert that all assertion conditions in the Law are co-related.
	 *
	 * @param bp
	 *            Branching Process of the refined Petri net
	 */
	public void validityAssertion(final BranchingProcess<LETTER, PLACE> bp) {
		final ICoRelation<LETTER, PLACE> coRelation = bp.getCoRelation();
		final List<Condition<LETTER, PLACE>> lawConditions = new ArrayList<>(mLaw);
		for (int i = 0; i < lawConditions.size(); i++) {
			for (int j = i + 1; j < lawConditions.size(); j++) {
				assert coRelation.isInCoRelation(lawConditions.get(i),
						lawConditions.get(j)) : "Conditions in Law are not co-related";
			}
		}
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
