package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.util.ArrayList;
import java.util.List;

/**
 * Class to create a tree for the tree automaton.
 * @author grugelt@uni-freiburg.de
 */
public class Tree<LETTER> implements ITreeRun<LETTER> {

	private final List<Tree<LETTER>> children;
	private final LETTER symbol;
	
	public Tree(LETTER symbol) {
		this.children = new ArrayList<Tree<LETTER>>();
		this.symbol = symbol;
	}
	
	
	public Tree(LETTER symbol, List<Tree<LETTER>> children) {
		this.children = children;
		this.symbol = symbol;
	}
	
	public void addChild(Tree<LETTER> child) {
		children.add(child);
	}
	
	public List<Tree<LETTER>> getChildren() {
		return this.children;
	}
	

	public String toString() {
		String res = symbol.toString();
		if (!getChildren().isEmpty()) {
			res += " ( ";
			for (Tree<LETTER> child : getChildren()) {
				res += child.toString() + ", ";
			}
			res += " ) ";
		}
		return res;
	}

	@Override
	public LETTER getRoot() {
		return symbol;
	}
	
 }
