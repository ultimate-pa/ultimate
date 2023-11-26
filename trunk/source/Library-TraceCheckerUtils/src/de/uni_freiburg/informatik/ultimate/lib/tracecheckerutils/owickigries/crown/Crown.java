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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

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

	public Crown(final BranchingProcess<LETTER, PLACE> bp) {
		mBp = bp;
		mCrown = new HashSet<>();
	}

	private Set<Set<Condition<LETTER, PLACE>>> getAllCrownCuts() {
		final var crownCuts = new HashSet<Set<Condition<LETTER, PLACE>>>();
		for (final Rook<PLACE, LETTER> rook : mCrown) {
			final var rookCensus = rook.getCensus();
			crownCuts.addAll(rookCensus);
		}
		return crownCuts;
	}

	private List<ImmutableList<Condition<LETTER, PLACE>>> computeCuts() {
		final var corelation = mBp.getCoRelation();

		final Condition<LETTER, PLACE>[] conditions = mBp.getConditions().toArray(Condition[]::new);
		final var cosets = new ArrayList<ImmutableList<Condition<LETTER, PLACE>>>();

		// worklist entries have the form Pair<ImmutableList<Condition>, int>(coset, minIndex)
		// Each pair in the worklist consists of a co-set (as list) and an index which identifies a suffix of the
		// conditions array. The suffix describes all conditions which may yet be added to the co-set.
		final var worklist = new ArrayDeque<Pair<ImmutableList<Condition<LETTER, PLACE>>, Integer>>();
		worklist.add(new Pair<>(ImmutableList.empty(), 0));

		while (!worklist.isEmpty()) {
			final var pair = worklist.pop();
			final var coset = pair.getFirst();
			final int minIndex = pair.getSecond();
			boolean isMaximal = true;

			ImmutableList<Condition<LETTER, PLACE>> extendedCoset = null;

			// See if any of the remaining candidates in conditions[minIndex..] can be added to the co-set.
			// If so, add them and push the result on the worklist.
			for (int i = minIndex; i < conditions.length; ++i) {
				final Condition<LETTER, PLACE> candidate = conditions[i];
				final boolean acceptCandidate = corelation.isCoset(coset, candidate);
				if (acceptCandidate) {
					// As an optimization, we do not push the extended co-set onto the worklist immediately.
					// By postponing, we avoid re-checking the co-relation wrt the next few conditions which
					// can already not be added to coset, let alone extendedCoset.
					if (extendedCoset != null) {
						worklist.push(new Pair<>(extendedCoset, i));
					}

					isMaximal = false;
					extendedCoset = new ImmutableList<>(candidate, coset);
				}
			}
			if (extendedCoset != null) {
				worklist.push(new Pair<>(extendedCoset, conditions.length));
			}

			// See if any condition in conditions[0..minIndex-1] can be added to the coset.
			// If so, the current co-set is not maximal.
			// We do not add the extended co-set to the worklist in this case; the algorithm should have done so before.
			for (int i = 0; isMaximal && i < minIndex; ++i) {
				isMaximal &= coset.contains(conditions[i]) || !corelation.isCoset(coset, conditions[i]);
			}

			// If the current coset is maximal, add its marking to the results.
			if (isMaximal) {
				cosets.add(coset);
			}
		}

		return cosets;
	}

	private boolean crownContainsAllCuts() {
		final var crownMarkings = getAllCrownCuts();
		final var branchingProcessCuts = computeCuts();
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

	/**
	 * Assert validity for the law and Kingdom
	 *
	 * @param placesCoRelation
	 *            Contains the information about the corelation of the Places.
	 * @param assertConds
	 *            Assertion Conditions of the refined Petri Net
	 */
	public void validityAssertion(final PlacesCoRelation<PLACE, LETTER> placesCoRelation,
			final Set<Condition<LETTER, PLACE>> assertConds) {
		for (final Rook<PLACE, LETTER> rook : mCrown) {
			rook.validityAssertion(mBp, placesCoRelation, assertConds);
		}
		assert crownContainsAllCuts() : "Crown does not contain all cosets of the refined Petri nets branching process";
	}

}
