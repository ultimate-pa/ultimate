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
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Data structure for sharing information between Petri net difference
 * operations. This information can guide the {@link Difference} operation by
 * providing information that are not known without inferring the reachable
 * (resp. vital) transitions of the result in advance.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class DifferenceSynchronizationInformation<LETTER, PLACE> {
	/**
	 * Letters for which the subtrahend DFA actually has a transition that changes
	 * the state. In on-demand constructions, this information can be more precise
	 * than mUniversalLoopers because the user cannot foresee the construction
	 * process.
	 */
	private final Set<LETTER> mChangerLetters;

	private final HashRelation<ITransition<LETTER, PLACE>, PLACE> mSelfloops;
	private final HashRelation<ITransition<LETTER, PLACE>, PLACE> mStateChangers;
	private final HashRelation<ITransition<LETTER, PLACE>, PLACE> mBlockingTransitions;
	private final Set<ITransition<LETTER, PLACE>> mContributingTransitions;

	@Deprecated
	public DifferenceSynchronizationInformation() {
		mChangerLetters = new HashSet<>();
		mSelfloops = new HashRelation<>();
		mStateChangers = new HashRelation<>();
		mBlockingTransitions = new HashRelation<>();
		mContributingTransitions = new HashSet<>();
	}

	public DifferenceSynchronizationInformation(final Set<LETTER> changerLetters,
			final HashRelation<ITransition<LETTER, PLACE>, PLACE> selfloops,
			final HashRelation<ITransition<LETTER, PLACE>, PLACE> stateChangers,
			final Set<ITransition<LETTER, PLACE>> contributingTransitions,
			final HashRelation<ITransition<LETTER, PLACE>, PLACE> blockingTransitions) {
		super();
		mChangerLetters = changerLetters;
		mSelfloops = selfloops;
		mStateChangers = stateChangers;
		mContributingTransitions = contributingTransitions;
		mBlockingTransitions = blockingTransitions;
	}

	public Set<LETTER> getChangerLetters() {
		return mChangerLetters;
	}

	public HashRelation<ITransition<LETTER, PLACE>, PLACE> getSelfloops() {
		return mSelfloops;
	}

	public HashRelation<ITransition<LETTER, PLACE>, PLACE> getStateChangers() {
		return mStateChangers;
	}

	public HashRelation<ITransition<LETTER, PLACE>, PLACE> getBlockingTransitions() {
		return mBlockingTransitions;
	}

	public Set<ITransition<LETTER, PLACE>> getContributingTransitions() {
		return mContributingTransitions;
	}

	@Deprecated
	public DifferenceSynchronizationInformation<LETTER, PLACE> filter(
			final Set<ITransition<LETTER, PLACE>> transitions) {
		final DifferenceSynchronizationInformation<LETTER, PLACE> result = new DifferenceSynchronizationInformation<>();
		result.getChangerLetters().addAll(mChangerLetters);
		for (final Entry<ITransition<LETTER, PLACE>, HashSet<PLACE>> entry : mSelfloops.entrySet()) {
			result.getSelfloops().addAllPairs(entry.getKey(), entry.getValue());
		}
		for (final Entry<ITransition<LETTER, PLACE>, HashSet<PLACE>> entry : mStateChangers.entrySet()) {
			result.getStateChangers().addAllPairs(entry.getKey(), entry.getValue());
		}
		result.getContributingTransitions().addAll(transitions);
		return result;
	}

}
