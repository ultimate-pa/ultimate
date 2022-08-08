package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;

/*
 * Object containing the marking at some index of some (imagined) firing sequence, the honda marking of that fire sequence if
 * the index is beyond the stem of the lassoword, and a boolean denoting if up until that point of the fire sequence during the
 * loop part of the lasso word there was a token shot inside an accepting place of the Petri net.
 * 
 * @param <LETTER>
 *            Symbol. Type of the symbols used as alphabet.
 * @param <STATE>
 *            Content. Type of the labels ("the content") of the automata states.
 */
public class MarkingOfFireSequence<LETTER, PLACE> {
	private final Marking<LETTER, PLACE> mMarking;
	private Marking<LETTER, PLACE> mHondaMarkingOfFireSequence;
	private final boolean mAcceptingPlaceSeenInLoop;

	/*
	 * Constructor.
	 * 
	 * @param <marking> The marking with {@link Marking}.
	 * 
	 * @param <hondaMarking> Hondamarking (The first marking of the loop part of the firing sequence). Defaults to the
	 * initial marking if the loop part of the word wasnt reached yet.
	 * 
	 * @param <acceptingStateSeen> Boolean denoting if up until that point of the fire sequence there was a token shot
	 * inside an accepting place of the Petri net.
	 */
	public MarkingOfFireSequence(final Marking<LETTER, PLACE> marking, final Marking<LETTER, PLACE> hondaMarking,
			final boolean acceptingStateSeen) {
		mMarking = marking;
		mHondaMarkingOfFireSequence = hondaMarking;
		mAcceptingPlaceSeenInLoop = acceptingStateSeen;
	}

	public Marking<LETTER, PLACE> getMarking() {
		return mMarking;
	}

	public Marking<LETTER, PLACE> getHondaMarkingOfFireSequence() {
		return mHondaMarkingOfFireSequence;
	}

	public void setHondaMarkingOfFireSequence(Marking<LETTER, PLACE> newHondaMarking) {
		mHondaMarkingOfFireSequence = newHondaMarking;
	}

	public boolean getAcceptingPlaceSeenInLoopBoolean() {
		return mAcceptingPlaceSeenInLoop;
	}

}
