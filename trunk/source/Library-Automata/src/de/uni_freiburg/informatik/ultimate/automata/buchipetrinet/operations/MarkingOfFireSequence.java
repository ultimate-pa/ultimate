package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;

/*
 * Object containing the marking of some (imagined) firing sequence, the index of that fire sequence which the marking is at,
 * and a boolean denoting if up until that point of the fire sequence during the loop part of the lasso word there was a token
 * shot inside an accepting place of the Petri net.
 * 
 * @param <LETTER>
 *            Symbol. Type of the symbols used as alphabet.
 * @param <STATE>
 *            Content. Type of the labels ("the content") of the automata states.
 */
public class MarkingOfFireSequence<LETTER, PLACE> {
	private final Marking<LETTER, PLACE> mMarking;
	private final int mRunposition;
	private final boolean mAcceptingPlaceSeenInLoop;

	/*
	 * Constructor.
	 * 
	 * @param <marking> The marking with {@link Marking}.
	 * 
	 * @param <position> Index of firing sequence where marking is at.
	 * 
	 * @param <acceptingStateSeen> Boolean denoting if up until that point of the fire sequence there was a token shot
	 * inside an accepting place of the Petri net.
	 */
	public MarkingOfFireSequence(final Marking<LETTER, PLACE> marking, final Integer position,
			final Boolean acceptingStateSeen) {
		mMarking = marking;
		mRunposition = position;
		mAcceptingPlaceSeenInLoop = acceptingStateSeen;
	}

	public Marking<LETTER, PLACE> getMarking() {
		return mMarking;
	}

	public Integer getRunPosition() {
		return mRunposition;
	}

	public Boolean getAcceptingPlaceSeenInLoopBoolean() {
		return mAcceptingPlaceSeenInLoop;
	}

}
