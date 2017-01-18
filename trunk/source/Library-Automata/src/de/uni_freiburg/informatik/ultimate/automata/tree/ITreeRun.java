package de.uni_freiburg.informatik.ultimate.automata.tree;

public interface ITreeRun<LETTER, STATE> {
	
	public ITreeAutomatonBU<LETTER, STATE> getAutomaton();
	
	public Tree<LETTER> getTree();
	
	public STATE getRoot();
	
	public LETTER getRootSymbol();
}
