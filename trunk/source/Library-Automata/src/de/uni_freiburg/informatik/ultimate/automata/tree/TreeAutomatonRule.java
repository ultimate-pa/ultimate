package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.util.List;

public class TreeAutomatonRule<LETTER, STATE> {
	private LETTER letter;
	private List<STATE> src;
	private STATE dest;
	
	public TreeAutomatonRule(LETTER letter, List<STATE> src, STATE dest) {
		this.letter = letter;
		this.src = src;
		this.dest = dest;
	}
	
	public List<STATE> getSource() {
		return src;
	}
	public LETTER getLetter() {
		return letter;
	}
	public STATE getDest() {
		return dest;
	}
	public int getArity() {
		return src != null ? src.size() : 0;
	}
	public String toString() {
		return "(" + src.toString() + " ~~ " + letter.toString() + " ~~> " + dest.toString() + ")";
	}
}
