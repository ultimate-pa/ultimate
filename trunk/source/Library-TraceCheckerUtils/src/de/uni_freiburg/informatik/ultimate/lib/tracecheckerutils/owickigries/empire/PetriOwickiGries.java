/*
 * Copyright (C) 2023 Matthias Zumkeller
 * Copyright (C) 2023 University of Freiburg
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

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class PetriOwickiGries<LETTER, PLACE> {

	private final BranchingProcess<LETTER, PLACE> mBp;
	private final Set<Condition<LETTER, PLACE>> mConditions;
	private final Set<Condition<LETTER, PLACE>> mOriginalConditions;
	private final Set<Condition<LETTER, PLACE>> mAssertionConditions;
	private final Set<PLACE> mOriginalPlaces;
	private final IPetriNet<LETTER, PLACE> mNet;
	private final Crown<PLACE, LETTER> mCrown;

	/**
	 *
	 * @param bp
	 *            finite prefix of unfolding for the refined net
	 * @param net
	 *            the original Petri program
	 */
	public PetriOwickiGries(final BranchingProcess<LETTER, PLACE> bp, final IPetriNet<LETTER, PLACE> net) {
		mBp = bp;
		mNet = net;
		mOriginalPlaces = mNet.getPlaces();
		mConditions = mBp.getConditions().stream().collect(Collectors.toSet());
		mOriginalConditions = getOrigConditions();
		mAssertionConditions = DataStructureUtils.difference(mConditions, mOriginalConditions);
		mCrown = getCrown();
	}

	private Crown<PLACE, LETTER> getCrown() {
		final CrownConstruction<PLACE, LETTER> crownConstruction =
				new CrownConstruction<>(mBp, mOriginalConditions, mAssertionConditions);
		return crownConstruction.getCrown();
	}

	private Set<Condition<LETTER, PLACE>> getOrigConditions() {
		final Set<Condition<LETTER, PLACE>> conditions = new HashSet<>();
		for (final Condition<LETTER, PLACE> cond : mBp.getConditions()) {
			if (mOriginalPlaces.contains(cond.getPlace())) {
				conditions.add(cond);
			}
		}
		return conditions;
	}
}
