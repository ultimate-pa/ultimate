package de.uni_freiburg.informatik.ultimate.automata.tree;

public interface ITreeRun<LETTER, STATE> {
	
	public ITreeAutomaton<LETTER, STATE> getAutomaton();
	
	public Tree<LETTER> getTree();
	
	public STATE getRoot();
	
	public LETTER getRootSymbol();
}
