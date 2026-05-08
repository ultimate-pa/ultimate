/*
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE Regression Test Library.
 *
 * The ULTIMATE Regression Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Regression Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Regression Test Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Regression Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Regression Test Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.pea;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

/**
 * This class implements an algorithm for minimizing Phase Event Automata as described in ... TODO
 *
 * @author Lena Funk
 */

public class PEAMinimization {

	public static final String MIN_POSTFIX = "_min";
	private final PhaseEventAutomata mPEAtoMinimize;
	private final PhaseEventAutomata mTotalisedPEA;
	private final PhaseEventAutomata mMinimizedPEA;
	private final PEAComplement mPEAComplement;
	private static HashMap<CDD, Set<Phase>> mPartitionByClockInv;
	UnionFind<Phase> mEquivalenceClasses;
	// Key: Equivalence Class Representative, Value: merged locations
	private static HashMap<Phase, Phase> mMergedLocations;

	public PEAMinimization(final PhaseEventAutomata peaToMinimize) {
		mPEAtoMinimize = peaToMinimize;
		mEquivalenceClasses = new UnionFind<>();
		mPEAComplement = new PEAComplement(mPEAtoMinimize);
		mTotalisedPEA = mPEAComplement.getTotalisedPEA();
		mPartitionByClockInv = new HashMap<>();
		createPartitionByClockInv(mTotalisedPEA.getPhases());
		mMinimizedPEA = minimize(mTotalisedPEA);
	}

	private static void createPartitionByClockInv(final List<Phase> phases) {
		for (final Phase phase : phases) {
			final CDD clockInv = phase.getClockInvariant();
			Set<Phase> set = mPartitionByClockInv.get(clockInv);
			if (set == null) {
				set = new HashSet<>();
				mPartitionByClockInv.put(clockInv, set);
			}
			set.add(phase);
		}
	}

	public static Boolean isMergable(final Phase location1, final Phase location2) {
		// check if the two locations are successor equivalent
		final List<Transition> transitionsLocation1 = location1.getTransitions();
		final List<Transition> transitionsLocation2 = location2.getTransitions();

		// if location1 and location2 are mergeable, both should have a transition to a destination location
		// we need this HashMap to check if those transitions are enabled under the same circumstances
		final HashMap<Phase, Set<Transition>> transitionsByDestination = new HashMap<>();

		// these are the destinations of the outgoing transitions of location1 and location2
		// location1 and location2 are only mergeable if they are successor equivalent, as in:
		// they have the same "destinations"
		final Set<Phase> destinations1 = new HashSet<>();
		final Set<Phase> destinations2 = new HashSet<>();

		// here we collect the destinations of outgoing transitions of location1 and location2, to later compare them
		// to check if they are successor equivalent
		for (final Transition t : transitionsLocation1) {
			final Phase destination = t.getDest();
			// use the representative of the equivalence class of the destination
			// final Phase destinationRepresentative = uf.find(destination);

			destinations1.add(destination);

			Set<Transition> set = transitionsByDestination.get(destination);
			if (set == null) {
				set = new HashSet<>();
				transitionsByDestination.put(destination, set);
			}
			set.add(t);
		}

		for (final Transition t : transitionsLocation2) {
			final Phase destination = t.getDest();
			// use the representative of the equivalence class of the destination
			// final Phase destinationRepresentative = uf.find(destination);

			destinations2.add(destination);

			Set<Transition> set = transitionsByDestination.get(destination);
			if (set == null) {
				set = new HashSet<>();
				transitionsByDestination.put(destination, set);
			}
			set.add(t);
		}

		// if the two locations are not successor equivalent, they cant be merged
		if (!destinations1.equals(destinations2)) {
			return false;
		}
		// if they are, we check if the guards and invariants (of the two locations) imply each other

		for (final HashMap.Entry<Phase, Set<Transition>> entry : transitionsByDestination.entrySet()) {

			final Phase destination = entry.getKey();

			final List<Transition> transitions = new ArrayList<>(entry.getValue());

			// I assume that no PEA-location has more than 1 transition to a destination location
			// so in total, for each destination we have two transitions
			assert (transitions.size() == 2);

			final Transition transition1 = transitions.get(0);
			final Transition transition2 = transitions.get(1);

			final CDD formula1 =
					transition1.getGuard().and(destination.getStateInvariant().and(destination.getClockInvariant()));
			final CDD formula2 =
					transition2.getGuard().and(destination.getStateInvariant().and(destination.getClockInvariant()));

			if (!(formula1.implies(formula2) && (formula2.implies(formula1)))) {
				return false;
			}

		}
		return true;
	}

	public HashMap<CDD, Set<Phase>> getPartitionByClockInv() {
		return mPartitionByClockInv;
	}

	public void mergeLocations() {
		// here we merge a whole equivalence class into one location
		for (final Set<Phase> equivalenceClass : mEquivalenceClasses.getAllEquivalenceClasses()) {
			final List<Phase> equivalenceClassList = new ArrayList<>(equivalenceClass);
			assert (equivalenceClass.size() >= 1);
			final Phase rep = equivalenceClassList.get(0);

			final Phase mergedLocation = new Phase(rep.getName(), CDD.FALSE, rep.getClockInv());

			for (final Phase location : equivalenceClass) {
				// generate state invariant
				final CDD mergedStateInv = mergedLocation.getStateInv();
				mergedLocation.setStateInv(mergedStateInv.or(location.getStateInv()));

			}
			if (!rep.getTerminal()) {
				mergedLocation.setTerminal(false);
			}
			mMergedLocations.put(rep, mergedLocation);

		}
	}

	public void mergeOutgoingTransitions() {
		for (final Phase rep : mMergedLocations.keySet()) {
			final HashSet<Phase> addedDestinations = new HashSet<>();
			final Phase mergedLocation = mMergedLocations.get(rep);
			for (final Transition outgoingTransition : rep.getTransitions()) {
				final Phase destination = outgoingTransition.getDest();
				final Phase destinationRep = mEquivalenceClasses.find(destination);

				// skip if we already have a transition to destination
				// skip if transition is "internal" to the equivalence class
				if (!addedDestinations.add(destinationRep) || rep == destinationRep) {
					continue;
				}

				final Phase mergedDestination = mMergedLocations.get(destinationRep);
				mergedLocation.addTransition(mergedDestination, outgoingTransition.getGuard(),
						outgoingTransition.getResets());

			}

			// add stutter loop
			CDD loopGuard = CDD.TRUE;
			if (rep.getClockInv().isTimed()) {
				loopGuard = RangeDecision.strict(rep.getClockInv());
			}
			mergedLocation.addTransition(mergedLocation, loopGuard, null);
		}
	}

	private void mergeIncomingTransitions() {
		for (final Phase rep : mMergedLocations.keySet()) {
			final HashSet<Phase> addedSources = new HashSet<>();
			final Phase mergedLocation = mMergedLocations.get(rep);
			for (final Transition incomingTransition : rep.getIncomingTransitions()) {
				final Phase source = incomingTransition.getSrc();
				final Phase sourceRep = mEquivalenceClasses.find(source);

				// skip if transition is "internal" to the equivalence class
				if (rep == sourceRep) {
					continue;
				}
				if (!addedSources.add(sourceRep)) {
					// TODO
				}
			}
		}
	}

	public PhaseEventAutomata minimize(final PhaseEventAutomata sourcePea) {

		for (final Entry<CDD, Set<Phase>> entry : mPartitionByClockInv.entrySet()) {
			final ArrayList<Phase> locations = new ArrayList<>(entry.getValue());

			for (final Phase location : locations) {
				mEquivalenceClasses.makeEquivalenceClass(location);
			}

			// compute equivalence class
			boolean changed;
			do {
				changed = false;

				for (int i = 0; i < locations.size(); i++) {
					for (int j = i + 1; j < locations.size(); j++) {

						final Phase location1 = locations.get(i);
						final Phase location2 = locations.get(j);

						if (mEquivalenceClasses.find(location1).equals(mEquivalenceClasses.find(location2))) {
							continue;
						}

						if (isMergable(location1, location2) && mEquivalenceClasses.union(location1, location2)) {
							changed = true;
						}
					}
				}

			} while (changed);
		}

		mergeLocations();
		mergeOutgoingTransitions();

		// TODO add initial locations
		final PhaseEventAutomata minimizedPEA = new PhaseEventAutomata(sourcePea.getName() + MIN_POSTFIX,
				new ArrayList<>(mMergedLocations.values()), null);
		return minimizedPEA;
	}

}
