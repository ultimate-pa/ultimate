package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.util.List;

/**
 * Rule of a TreeAutomaton. F(q1, ..., qn) -> p
 * @author mostafa (mostafa.amin93@gmail.com)
 * 
 * @param <LETTER> Letters of the automaton.
 * @param <STATE> States of the automaton.
 */
public class TreeAutomatonRule<LETTER, STATE> {
	private final LETTER letter;
	private final List<STATE> src;
	private final STATE dest;
	
	/**
	 * Construct a rule: letter(src) -> dest
	 * @param letter
	 * @param src
	 * @param dest
	 */
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
	@Override
	public String toString() {
		return "(" + src.toString() + " ~~ " + letter.toString() + " ~~> " + dest.toString() + ")";
	}
}
