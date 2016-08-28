package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.util.ArrayList;
import java.util.List;

/**
 * Class to create a tree for the tree automaton.
 * @author mostafa.amin93@gmail.com, grugelt@uni-freiburg.de
 */
public class Tree<LETTER> {

	private final List<Tree<LETTER>> children;
	private final LETTER symbol;
	
	public Tree(LETTER symbol) {
		this.children = new ArrayList<Tree<LETTER>>();
		this.symbol = symbol;
	}
	
	public Tree(LETTER symbol, List<Tree<LETTER>> children) {
		this.children = new ArrayList<Tree<LETTER>>();
		for (Tree<LETTER> child : children) {
			if (child != null && child.symbol != null) {
				this.children.add(child);
			}
		}
		this.symbol = symbol;
	}
	
	public List<Tree<LETTER>> getChildren() {
		return this.children;
	}

	public String toString() {
		String res = symbol.toString();
		if (!getChildren().isEmpty()) {
			res += getChildren();
		}
		return res;
	}
	
 }
