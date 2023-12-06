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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.crown;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;

/**
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 * @param <LETTER>
 *            The type of statements in the Petri program
 */

public final class Crown<PLACE, LETTER> {

	private final Set<Rook<PLACE, LETTER>> mCrown;

	private final BranchingProcess<LETTER, PLACE> mBp;

	public Crown(final BranchingProcess<LETTER, PLACE> bp, final Set<Rook<PLACE, LETTER>> crown) {
		mBp = bp;
		mCrown = crown;
	}

	private Set<Set<Condition<LETTER, PLACE>>> getAllCrownCuts() {
		final var crownCuts = new HashSet<Set<Condition<LETTER, PLACE>>>();
		for (final Rook<PLACE, LETTER> rook : mCrown) {
			final var rookCensus = rook.getCensus();
			crownCuts.addAll(rookCensus);
		}
		return crownCuts;
	}

	private boolean crownContainsAllCuts() {
		final var crownMarkings = getAllCrownCuts();
		final var branchingProcessCuts = mBp.computeCuts();
		for (final ImmutableList<Condition<LETTER, PLACE>> branchingProcessCoset : branchingProcessCuts) {
			final Set<Condition<LETTER, PLACE>> coset =
					branchingProcessCoset.stream().map(condition -> condition).collect(Collectors.toSet());
			if (!crownMarkings.contains(coset)) {
				return false;
			}
		}
		return true;
	}

	public Set<Rook<PLACE, LETTER>> getRooks() {
		return mCrown;
	}

	public void addRook(final Rook<PLACE, LETTER> rook) {
		mCrown.add(rook);
	}

	public void addRook(final Set<Rook<PLACE, LETTER>> rooks) {
		mCrown.addAll(rooks);
	}

	public boolean removeRook(final Rook<PLACE, LETTER> rook) {
		if (mCrown.contains(rook)) {
			mCrown.remove(rook);
			return true;
		}
		return false;
	}

	public boolean removeRook(final Set<Rook<PLACE, LETTER>> rooks) {
		if (mCrown.containsAll(rooks)) {
			mCrown.removeAll(rooks);
			return true;
		}
		return false;
	}

	public long getNumKingdoms() {
		return mCrown.size();
	}

	public long getAssertionSize() {
		final long assertionSize =
				mCrown.stream().collect(Collectors.summingLong(x -> x.getLaw().getConditions().size()));
		return assertionSize;
	}

	public long getCrownSize() {
		return getNumKingdoms() + getAssertionSize();
	}

	/**
	 * Assert validity for the law and Kingdom
	 *
	 * @param placesCoRelation
	 *            Contains the information about the corelation of the Places.
	 * @param assertConds
	 *            Assertion Conditions of the refined Petri Net
	 */
	public boolean validityAssertion(final PlacesCoRelation<PLACE, LETTER> placesCoRelation,
			final Set<Condition<LETTER, PLACE>> assertConds) {
		for (final Rook<PLACE, LETTER> rook : mCrown) {
			if (!rook.validityAssertion(mBp, placesCoRelation, assertConds)) {
				assert false;
				return false;
			}
		}
		if (!crownContainsAllCuts()) {
			assert false : "Crown does not contain all cuts of the refined Petri nets branching process";
			return false;
		}
		return true;
	}
}
