package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;

public class PetriNetLassoRun<LETTER, PLACE> {
	private final PetriNetRun<LETTER, PLACE> mStem;
	private final PetriNetRun<LETTER, PLACE> mLoop;

	public PetriNetLassoRun(final PetriNetRun<LETTER, PLACE> stem, final PetriNetRun<LETTER, PLACE> loop) {
		mStem = stem;
		mLoop = loop;
	}

	public PetriNetRun<LETTER, PLACE> getStem() {
		return mStem;
	}

	public PetriNetRun<LETTER, PLACE> getLoop() {
		return mLoop;
	}

	public NestedLassoWord<LETTER> getNestedLassoWord() {
		return new NestedLassoWord<>(NestedWord.nestedWord(getStem().getWord()),
				NestedWord.nestedWord(getLoop().getWord()));
	}
	// TODO
	// public NestedLassoRun<LETTER, STATE>();

}
