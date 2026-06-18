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
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
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
	List<InitialTransition> mMergedInitialTransitions;

	private final Set<String> mConstVars;

	public PEAMinimization(final PhaseEventAutomata peaToMinimize) {
		mPEAtoMinimize = peaToMinimize;
		mEquivalenceClasses = new UnionFind<>();
		mConstVars = Collections.emptySet();
		mPEAComplement = new PEAComplement(mPEAtoMinimize);
		mTotalisedPEA = mPEAComplement.getTotalisedPEA();
		mPartitionByClockInv = new HashMap<>();
		mMergedLocations = new HashMap<>();
		createPartitionByClockInv(mTotalisedPEA.getPhases());
		mMergedInitialTransitions = new ArrayList<>();
		mMinimizedPEA = minimize(mTotalisedPEA);

	}

	public PEAMinimization(final PhaseEventAutomata peaToMinimize, final Set<String> constVars) {
		mPEAtoMinimize = peaToMinimize;
		mEquivalenceClasses = new UnionFind<>();
		mConstVars = constVars;
		mPEAComplement = new PEAComplement(mPEAtoMinimize, mConstVars);
		mTotalisedPEA = mPEAComplement.getTotalisedPEA();
		mPartitionByClockInv = new HashMap<>();
		mMergedLocations = new HashMap<>();
		createPartitionByClockInv(mTotalisedPEA.getPhases());
		mMergedInitialTransitions = new ArrayList<>();
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

	private static HashMap<Phase, Set<Transition>> computeOutgoingTransitions(final Set<Phase> phaseSet) {
		final HashMap<Phase, Set<Transition>> outgoingTransitions = new HashMap<>();
		for (final Phase location : phaseSet) {
			for (final Transition transition : location.getTransitions()) {
				final Phase destination = transition.getDest();
				// not an internal transition
				if (phaseSet.contains(destination)) {
					continue;
				}
				Set<Transition> set = outgoingTransitions.get(destination);
				if (set == null) {
					set = new HashSet<>();
					outgoingTransitions.put(destination, set);
				}
				set.add(transition);
			}
		}
		return outgoingTransitions;
	}

	public static Boolean isMergable(final Phase location1, final Phase location2) {
		// check if the two locations are successor equivalent
		if (location1.isTerminal() && !location2.isTerminal() || !location1.isTerminal() && location2.isTerminal()) {
			return false;
		}
		final Set<Phase> locations = new HashSet<>();
		locations.add(location1);
		locations.add(location2);

		HashMap<Phase, Set<Transition>> transitionsByDestination = new HashMap<>();

		transitionsByDestination = computeOutgoingTransitions(locations);

		for (final Set<Transition> transitionSet : transitionsByDestination.values()) {
			if (transitionSet.size() != 2) {
				return false;
			}
			final List<Transition> transitions = new ArrayList<>(transitionSet);
			final Transition transition1 = transitions.get(0);
			final Transition transition2 = transitions.get(1);

			final CDD guard1 = transition1.getGuard();
			final CDD guard2 = transition2.getGuard();

			if (!(guard1.implies(guard2) && (guard2.implies(guard1)))) {
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
			final Phase rep = mEquivalenceClasses.find(equivalenceClassList.get(0));

			final Phase mergedLocation = new Phase(rep.getName() + "_merged", CDD.FALSE, rep.getClockInv());

			for (final Phase location : equivalenceClass) {
				// generate state invariant
				final CDD mergedStateInv = mergedLocation.getStateInv();
				mergedLocation.setStateInv(mergedStateInv.or(location.getStateInv()));

				if (location.isInit()) {
					mergedLocation.setInit(true);
				}

			}
			if (!rep.getTerminal()) {
				mergedLocation.setTerminal(false);
			}

			final List<RangeDecision> repModifiedConstraints = rep.getModifiedConstraints();
			final List<RangeDecision> mergedModifiedConstraints = new ArrayList<>();
			if (!repModifiedConstraints.isEmpty()) {
				for (final RangeDecision strictClockConstraint : repModifiedConstraints) {
					final String var = strictClockConstraint.getVar() + MIN_POSTFIX;
					final int val = strictClockConstraint.getVal(0);
					final int op = strictClockConstraint.getOp(0);
					final CDD mergedStrictClockConstraint = RangeDecision.create(var, op, val);
					mergedModifiedConstraints.add((RangeDecision) mergedStrictClockConstraint.getDecision());
				}
			}
			mergedLocation.setModifiedConstraints(mergedModifiedConstraints);

			final CDD clockInvRep = rep.getClockInv();

			CDD mergedClockInvariant = CDD.TRUE;
			if (clockInvRep.isTimed()) {
				final CDD invWithRenamedClock = CDD.addClockSuffixCDD(clockInvRep, MIN_POSTFIX);
				mergedClockInvariant = mergedClockInvariant.and(invWithRenamedClock);
			}

			mergedLocation.setClockInv(mergedClockInvariant);

			mMergedLocations.put(rep, mergedLocation);

		}
	}

	public void mergeOutgoingTransitions() {
		for (final Phase rep : mEquivalenceClasses.getAllRepresentatives()) {
			final HashSet<Phase> addedDestinations = new HashSet<>();
			final Phase mergedLocation = mMergedLocations.get(rep);
			for (final Transition outgoingTransition : rep.getTransitions()) {
				final Phase destination = outgoingTransition.getDest();
				final Phase destinationRep = mEquivalenceClasses.find(destination);
				final Set<Phase> destinationClass = mEquivalenceClasses.getContainingSet(destination);
				final CDD guard = outgoingTransition.getGuard();
				CDD mergedGuard = CDD.TRUE;

				if (guard.isTimed()) {
					final CDD guardWithRenamedClock = CDD.addClockSuffixCDD(guard, MIN_POSTFIX);
					mergedGuard = mergedGuard.and(guardWithRenamedClock);
				} else {
					mergedGuard = mergedGuard.and(guard);
				}

				if (destinationClass.size() > 1) {
					mergedGuard = mergedGuard.and(destination.getStateInv());
				}

				// skip if we already have a transition to destination
				// skip if transition is "internal" to the equivalence class
				if (!addedDestinations.add(destinationRep) || rep == destinationRep) {
					continue;
				}

				final String[] mergedResets = outgoingTransition.getResets().clone();

				for (int i = 0; i < mergedResets.length; i++) {
					mergedResets[i] = mergedResets[i] + MIN_POSTFIX;
				}

				final Phase mergedDestination = mMergedLocations.get(destinationRep);
				mergedLocation.addTransition(mergedDestination, mergedGuard, mergedResets);

			}

			// add stutter loop
			CDD loopGuard = CDD.TRUE;
			if (rep.getClockInv().isTimed()) {
				loopGuard = RangeDecision.strict(mergedLocation.getClockInv());
			}
			mergedLocation.addTransition(mergedLocation, loopGuard, new String[0]);
		}
	}

	private void mergeInitialTransitions() {
		for (final Phase rep : mMergedLocations.keySet()) {

			final ImmutableSet<Phase> equivalenceClass = mEquivalenceClasses.getEquivalenceClassMembers(rep);
			final HashSet<InitialTransition> initialTransitions = new HashSet<>();

			final Phase mergedLocation = mMergedLocations.get(rep);
			for (final Phase location : equivalenceClass) {
				if (location.isInit()) {
					final InitialTransition initialTransition = location.getInitialTransition();
					initialTransitions.add(initialTransition);
					mergedLocation.setInit(true);
				}

			}
			if (mergedLocation.isInit()) {
				CDD initialGuard = CDD.FALSE;
				for (final InitialTransition initialTransition : initialTransitions) {
					initialGuard = initialGuard
							.or(initialTransition.getGuard().and(initialTransition.getDest().getStateInv()));
				}
				final InitialTransition mergedInitialTransition = new InitialTransition(initialGuard, mergedLocation);
				mergedLocation.setInitialTransition(mergedInitialTransition);
				mMergedInitialTransitions.add(mergedInitialTransition);
			}
		}
	}

	public PhaseEventAutomata minimize(final PhaseEventAutomata sourcePea) {

		for (final Entry<CDD, Set<Phase>> entry : mPartitionByClockInv.entrySet()) {
			final ArrayList<Phase> locations = new ArrayList<>(entry.getValue());

			for (final Phase location : locations) {
				mEquivalenceClasses.makeEquivalenceClass(location);
			}

			// compute equivalence classes
			boolean changed;
			do {
				changed = false;

				for (int i = 0; i < locations.size(); i++) {
					for (int j = i + 1; j < locations.size(); j++) {

						final Phase location1 = locations.get(i);
						final Phase location2 = locations.get(j);

						if (isMergable(location1, location2)) {
							changed = mEquivalenceClasses.union(location1, location2);
						}
					}
				}

			} while (changed);
		}

		mergeLocations();
		mergeOutgoingTransitions();
		mergeInitialTransitions();

		final List<String> mergedClocks = new ArrayList<>();
		for (final String s : sourcePea.getClocks()) {
			mergedClocks.add(s + MIN_POSTFIX);
		}

		final PhaseEventAutomata minimizedPEA =
				new PhaseEventAutomata(sourcePea.getName() + MIN_POSTFIX, new ArrayList<>(mMergedLocations.values()),
						mMergedInitialTransitions, mergedClocks, new HashMap<>(sourcePea.getVariables()));
		return minimizedPEA;
	}

	public PhaseEventAutomata getTotalisedPEA() {
		return mTotalisedPEA;
	}

	public PhaseEventAutomata getMinimizedPEA() {
		return mMinimizedPEA;
	}
}
