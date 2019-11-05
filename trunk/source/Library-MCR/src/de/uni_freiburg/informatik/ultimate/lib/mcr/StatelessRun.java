package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;

public class StatelessRun<LETTER, STATE> implements IRun<LETTER, STATE> {
	private final Word<LETTER> mWord;

	public StatelessRun(final Word<LETTER> word) {
		mWord = word;
	}

	@Override
	public Word<LETTER> getWord() {
		return mWord;
	}

	@Override
	public LETTER getSymbol(final int position) {
		return mWord.getSymbol(position);
	}

	@Override
	public int getLength() {
		return mWord.length();
	}

	@Override
	public List<STATE> getStateSequence() {
		throw new UnsupportedOperationException(getClass().getName() + " cannot provide a state sequence");
	}

}
