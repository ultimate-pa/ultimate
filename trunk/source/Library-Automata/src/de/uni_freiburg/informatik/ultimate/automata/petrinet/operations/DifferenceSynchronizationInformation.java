/*
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Data structure for sharing information between Petri net difference operations. This information can guide the
 * {@link Difference} operation by providing information that are not known without inferring the reachable (resp.
 * vital) transitions of the result in advance.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class DifferenceSynchronizationInformation<LETTER, PLACE> {
	/**
	 * Letters for which the subtrahend DFA actually has a transition that changes the state. In on-demand
	 * constructions, this information can be more precise than mUniversalLoopers because the user cannot foresee the
	 * construction process.
	 */
	private final Set<LETTER> mChangerLetters;

	private final HashRelation<Transition<LETTER, PLACE>, PLACE> mSelfloops;
	private final HashRelation<Transition<LETTER, PLACE>, PLACE> mStateChangers;
	private final HashRelation<Transition<LETTER, PLACE>, PLACE> mBlockingTransitions;
	private final Set<Transition<LETTER, PLACE>> mContributingTransitions;
	/**
	 * If true, then every transition of a difference build according to these instructions will be a reachable
	 * transition.
	 */
	private final boolean mReachabilityPreserved;
	/**
	 * If true, then every transition of a difference build according to these instructions will be a vital transition.
	 */
	private final boolean mVitalityPreserved;

	public DifferenceSynchronizationInformation(final Set<LETTER> changerLetters,
			final HashRelation<Transition<LETTER, PLACE>, PLACE> selfloops,
			final HashRelation<Transition<LETTER, PLACE>, PLACE> stateChangers,
			final Set<Transition<LETTER, PLACE>> contributingTransitions,
			final HashRelation<Transition<LETTER, PLACE>, PLACE> blockingTransitions,
			final boolean reachabilityPreserved, final boolean vitalityPreserved) {
		super();
		mChangerLetters = changerLetters;
		mSelfloops = selfloops;
		mStateChangers = stateChangers;
		mContributingTransitions = contributingTransitions;
		mBlockingTransitions = blockingTransitions;
		mReachabilityPreserved = reachabilityPreserved;
		mVitalityPreserved = vitalityPreserved;
	}

	public Set<LETTER> getChangerLetters() {
		return mChangerLetters;
	}

	public HashRelation<Transition<LETTER, PLACE>, PLACE> getSelfloops() {
		return mSelfloops;
	}

	public HashRelation<Transition<LETTER, PLACE>, PLACE> getStateChangers() {
		return mStateChangers;
	}

	public HashRelation<Transition<LETTER, PLACE>, PLACE> getBlockingTransitions() {
		return mBlockingTransitions;
	}

	public Set<Transition<LETTER, PLACE>> getContributingTransitions() {
		return mContributingTransitions;
	}

	public boolean isReachabilityPreserved() {
		return mReachabilityPreserved;
	}

	public boolean isVitalityPreserved() {
		return mVitalityPreserved;
	}

	public DifferenceSynchronizationInformation<LETTER, PLACE> transformThroughRemoveRedundantFlow(
			final HashRelation<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> minuendTransition2differenceTransitions,
			final Map<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> differenceTransitions2projectedTransitions,
			final HashRelation<Transition<LETTER, PLACE>, PLACE> redundantSelfloopFlow,
			final Set<PLACE> redundantPlaces) {
		final HashRelation<Transition<LETTER, PLACE>, PLACE> selfloops = new HashRelation<>();
		for (final Entry<Transition<LETTER, PLACE>, HashSet<PLACE>> entry : mSelfloops.entrySet()) {
			for (final PLACE automatonState : entry.getValue()) {
				final Set<Transition<LETTER, PLACE>> differenceTransitions =
						minuendTransition2differenceTransitions.getImage(entry.getKey());
				assert !differenceTransitions.isEmpty() : "no corresponding transitions in difference";
				if (!isRedundantForAll(redundantSelfloopFlow, differenceTransitions, automatonState)) {
					final Transition<LETTER, PLACE> projectedTransition =
							differenceTransitions2projectedTransitions.get(differenceTransitions.iterator().next());
					selfloops.addPair(projectedTransition, automatonState);
				}
			}
		}
		final HashRelation<Transition<LETTER, PLACE>, PLACE> stateChangers = new HashRelation<>();
		for (final Entry<Transition<LETTER, PLACE>, HashSet<PLACE>> entry : mStateChangers.entrySet()) {
			final Set<Transition<LETTER, PLACE>> differenceTransitions =
					minuendTransition2differenceTransitions.getImage(entry.getKey());
			for (final PLACE automatonState : entry.getValue()) {
				if (!redundantPlaces.contains(automatonState)) {
					final Transition<LETTER, PLACE> projectedTransition =
							differenceTransitions2projectedTransitions.get(differenceTransitions.iterator().next());
					stateChangers.addPair(projectedTransition, automatonState);
				}
			}
		}
		final HashRelation<Transition<LETTER, PLACE>, PLACE> blockingTransitions = new HashRelation<>();
		for (final Entry<Transition<LETTER, PLACE>, HashSet<PLACE>> entry : mBlockingTransitions.entrySet()) {
			final Set<Transition<LETTER, PLACE>> differenceTransitions =
					minuendTransition2differenceTransitions.getImage(entry.getKey());
			if (!differenceTransitions.isEmpty()) {
				for (final PLACE automatonState : entry.getValue()) {
					final Transition<LETTER, PLACE> projectedTransition =
							differenceTransitions2projectedTransitions.get(differenceTransitions.iterator().next());
					if (!redundantPlaces.contains(automatonState)) {
						blockingTransitions.addPair(projectedTransition, automatonState);
					}
				}
			}
		}
		final Set<Transition<LETTER, PLACE>> contributingTransitions = mContributingTransitions.stream()
				.map(x -> differenceTransitions2projectedTransitions
						.get(minuendTransition2differenceTransitions.getImage(x).iterator().next()))
				.collect(Collectors.toSet());
		return new DifferenceSynchronizationInformation<>(mChangerLetters, selfloops, stateChangers,
				contributingTransitions, blockingTransitions, true, false);
	}

	private boolean isRedundantForAll(final HashRelation<Transition<LETTER, PLACE>, PLACE> redundantSelfloopFlow,
			final Set<Transition<LETTER, PLACE>> differenceTransitions, final PLACE automatonState) {
		return differenceTransitions.stream().allMatch(x -> redundantSelfloopFlow.containsPair(x, automatonState));
	}

	public boolean isCompatible(final IPetriNet<LETTER, PLACE> net) {
		if (!net.getAlphabet().containsAll(getChangerLetters())) {
			return false;
		}
		if (!net.getTransitions().containsAll(getStateChangers().getDomain())) {
			return false;
		}
		if (!net.getTransitions().containsAll(getSelfloops().getDomain())) {
			return false;
		}
		if (!net.getTransitions().containsAll(getBlockingTransitions().getDomain())) {
			return false;
		}
		return true;
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("DifferenceSynchronizationInformation [mChangerLetters=");
		builder.append(System.lineSeparator());
		builder.append(mChangerLetters);
		builder.append(System.lineSeparator());
		builder.append(", mSelfloops=");
		builder.append(System.lineSeparator());
		builder.append(mSelfloops);
		builder.append(System.lineSeparator());
		builder.append(", mStateChangers=");
		builder.append(System.lineSeparator());
		builder.append(mStateChangers);
		builder.append(System.lineSeparator());
		builder.append(", mBlockingTransitions=");
		builder.append(System.lineSeparator());
		builder.append(mBlockingTransitions);
		builder.append(System.lineSeparator());
		builder.append(", mContributingTransitions=");
		builder.append(System.lineSeparator());
		builder.append(mContributingTransitions);
		builder.append(System.lineSeparator());
		builder.append("]");
		return builder.toString();
	}

}
