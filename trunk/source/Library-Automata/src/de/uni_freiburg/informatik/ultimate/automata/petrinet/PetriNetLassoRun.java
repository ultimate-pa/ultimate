package de.uni_freiburg.informatik.ultimate.automata.petrinet;

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
}
