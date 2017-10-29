package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NwaOutgoingLetterAndTransitionAdapter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiComplementNCSBSimpleNwa;

public class ComplementNwaOutgoingLetterAndTransitionAdapter<LETTER, STATE> extends NwaOutgoingLetterAndTransitionAdapter<LETTER, STATE>{

	private final BuchiComplementNCSBSimpleNwa<LETTER, STATE> mComplementNwa;
	
	public ComplementNwaOutgoingLetterAndTransitionAdapter(
			final BuchiComplementNCSBSimpleNwa<LETTER, STATE> complementNwa) {
		super(complementNwa);
		mComplementNwa = complementNwa;
	}

	public boolean coveredBy(STATE fstState, STATE sndState) {
		return mComplementNwa.coveredBy(fstState, sndState);
	}

}
