package de.uni_freiburg.informatik.ultimate.automata;


public interface IRun<LETTER,STATE> {
	
	public Word<LETTER> getWord();
	
	public LETTER getSymbol(int i);
	
	public int getLength();

}
