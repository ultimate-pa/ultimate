package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/*
 * Object containing the marking at some index of some (imagined) firing sequence, the (indexed) honda marking(s) of
 * that fire sequence and an index denoting when in the firing sequence an accpeting place was last fired into with a
 * token.
 *
 * @param <LETTER>
 *            Symbol. Type of the symbols used as alphabet.
 * @param <STATE>
 *            Content. Type of the labels ("the content") of the automata states.
 */
public class MarkingOfFireSequence<LETTER, PLACE> {
	private final Marking<LETTER, PLACE> mMarking;
	/*
	 * Indexed hondamarkings of firing sequence of marking.
	 */
	private final Set<Pair<Marking<LETTER, PLACE>, Integer>> mHondaMarkingsOfFireSequence;
	private final int mFireSequenceIndex;
	private final int mLastIndexOfShootingAcceptingStateInFireSequence;

	/*
	 * Constructor.
	 *
	 * @param <marking> The marking with {@link Marking}.
	 *
	 * @param <hondaMarking> A marking which is produced after the firing of the loop part of a word during the a fire
	 * sequence. We also denote the index of the firing sequence when this marking is produced.
	 *
	 * @param <lastIndexOfShootingAcceptingStateInFireSequence> denoting at what index of a firing sequence an accepting
	 * place was last shot with a token.
	 */
	public MarkingOfFireSequence(final Marking<LETTER, PLACE> marking,
			final Set<Pair<Marking<LETTER, PLACE>, Integer>> hondaMarkings, final int fireSequenceIndex,
			final int lastIndexOfShootingAcceptingStateInFireSequence) {
		mMarking = marking;
		mHondaMarkingsOfFireSequence = hondaMarkings;
		mFireSequenceIndex = fireSequenceIndex;
		mLastIndexOfShootingAcceptingStateInFireSequence = lastIndexOfShootingAcceptingStateInFireSequence;
	}

	public final Marking<LETTER, PLACE> getMarking() {
		return mMarking;
	}

	public Set<Pair<Marking<LETTER, PLACE>, Integer>> getHondaMarkingsOfFireSequence() {
		return mHondaMarkingsOfFireSequence;
	}

	public void addHondaMarkingOfFireSequence(final Marking<LETTER, PLACE> newHondaMarking,
			final int hondaMarkingIndex) {
		mHondaMarkingsOfFireSequence.add(new Pair<>(newHondaMarking, hondaMarkingIndex));
	}

	public void clearHondaMarkingsOfFireSequence() {
		mHondaMarkingsOfFireSequence.clear();
	}

	public final int getfireSequenceIndex() {
		return mFireSequenceIndex;
	}

	public final int getLastIndexOfShootingAcceptingStateInFireSequence() {
		return mLastIndexOfShootingAcceptingStateInFireSequence;
	}

}
