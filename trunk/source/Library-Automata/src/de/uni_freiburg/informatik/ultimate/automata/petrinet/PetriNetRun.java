/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * A Petri net run is a sequence of markings <tt>m0 ... m_{n+1}</tt> and a word <tt>w_0 ... w_n</tt>.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            symbols type
 * @param <PLACE>
 *            place content type
 */
public class PetriNetRun<LETTER, PLACE> implements IRun<LETTER, Marking<PLACE>> {

	private final Word<LETTER> mWord;
	private final List<Marking<PLACE>> mMarkingSequence;
	private final List<Transition<LETTER, PLACE>> mTransitionSequence;

	/**
	 * Construct Petri net run of length 0.
	 *
	 * @param m0
	 *            initial marking
	 */
	public PetriNetRun(final Marking<PLACE> m0) {
		mWord = new NestedWord<>();
		mTransitionSequence = List.of();
		mMarkingSequence = List.of(m0);
	}

	/**
	 * Constructs Petri net run of length 1.
	 *
	 * @param m0
	 *            initial marking
	 * @param symbol
	 *            first symbol
	 * @param m1
	 *            next marking
	 */
	public PetriNetRun(final Marking<PLACE> m0, final Transition<LETTER, PLACE> transition, final Marking<PLACE> m1) {
		mTransitionSequence = List.of(transition);
		mWord = new NestedWord<>(transition.getSymbol(), NestedWord.INTERNAL_POSITION);
		mMarkingSequence = new ArrayList<>();
		mMarkingSequence.add(m0);
		mMarkingSequence.add(m1);
	}

	/**
	 * Constructs Petri net run of arbitrary length.
	 *
	 * @param sequenceOfMarkings
	 *            sequence of markings
	 * @param word
	 *            corresponding word
	 */
	public PetriNetRun(final List<Marking<PLACE>> sequenceOfMarkings, final Word<LETTER> word,
			final List<Transition<LETTER, PLACE>> transitions) {
		if (sequenceOfMarkings.size() - 1 != word.length()) {
			throw new IllegalArgumentException("run consists of word length +1 markings");
		}
		if (transitions.size() != word.length()) {
			throw new IllegalArgumentException("number of transitions differs from length of word");
		}
		mMarkingSequence = sequenceOfMarkings;
		mTransitionSequence = transitions;
		mWord = word;
	}

	@Override
	public LETTER getSymbol(final int pos) {
		return mWord.getSymbol(pos);
	}

	@Override
	public Word<LETTER> getWord() {
		return mWord;
	}

	/**
	 * @param pos
	 *            Position.
	 * @return marking at the given position
	 */
	public Marking<PLACE> getMarking(final int pos) {
		return mMarkingSequence.get(pos);
	}

	public Transition<LETTER, PLACE> getTransition(final int pos) {
		return mTransitionSequence.get(pos);
	}

	/**
	 * @param run2
	 *            Another run.
	 * @return A new run which is the concatenation of this and run2. This is not changed.
	 */
	public PetriNetRun<LETTER, PLACE> concatenate(final PetriNetRun<LETTER, PLACE> run2) {
		if (!getMarking(mMarkingSequence.size() - 1).equals(run2.getMarking(0))) {
			throw new IllegalArgumentException("can only concatenate runs where last Marking of first run and first "
					+ "Marking of second run coincide");
		}
		final List<Marking<PLACE>> concatMarkingSequence =
				DataStructureUtils.concat(mMarkingSequence, run2.mMarkingSequence.subList(1, run2.getLength()));
		final List<Transition<LETTER, PLACE>> concatTransitions =
				DataStructureUtils.concat(mTransitionSequence, run2.mTransitionSequence);
		final Word<LETTER> concatWord = mWord.concatenate(run2.getWord()); // TODO
		return new PetriNetRun<>(concatMarkingSequence, concatWord, concatTransitions);
	}

	@Override
	public int getLength() {
		return mMarkingSequence.size();
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		for (int i = 0; i < mWord.length(); i++) {
			sb.append(mMarkingSequence.get(i)).append(' ');
			sb.append(mWord.getSymbol(i)).append(' ');
		}
		sb.append(mMarkingSequence.get(mMarkingSequence.size() - 1));
		return sb.toString();
	}

	@Override
	public List<Marking<PLACE>> getStateSequence() {
		return mMarkingSequence;
	}

	/**
	 * Check if this run is actually possible in the given Petri net
	 *
	 * @param net
	 *            A Petri net
	 * @return true if the run can be replicated on the given net, false otherwise
	 * @throws PetriNetNot1SafeException
	 *             if the run (or some prefix of the run) can be replicated, but results in a marking where some place
	 *             has more than one token
	 */
	public boolean isRunOf(final IPetriNet<LETTER, PLACE> net) throws PetriNetNot1SafeException {
		final var initialMarking = new Marking<>(ImmutableSet.of(net.getInitialPlaces()));
		if (!mMarkingSequence.get(0).equals(initialMarking)) {
			return false;
		}

		var marking = initialMarking;
		for (int i = 0; i < mTransitionSequence.size(); ++i) {
			final var transition = mTransitionSequence.get(i);
			final var letter = mWord.getSymbol(i);
			if (!letter.equals(transition.getSymbol())) {
				return false;
			}

			if (!marking.isTransitionEnabled(transition)) {
				return false;
			}

			final var expectedMarking = marking.fireTransition(transition);
			final var actualMarking = mMarkingSequence.get(i + 1);
			if (!expectedMarking.equals(actualMarking)) {
				return false;
			}

			marking = actualMarking;
		}
		return true;
	}

	/**
	 * Check if the run is an accepting run of the given Petri net
	 *
	 * @param net
	 *            A Petri net, in which certain places are accepting
	 * @return true if the final marking of the run is accepting
	 */
	public boolean isAccepting(final IPetriNet<LETTER, PLACE> net) {
		return net.isAccepting(getMarking(mMarkingSequence.size() - 1));
	}
}
