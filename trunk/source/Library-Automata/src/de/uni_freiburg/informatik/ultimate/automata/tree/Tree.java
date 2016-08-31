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
	
	/**
	 * Construct a tree with root symbol.
	 * @param symbol
	 */
	public Tree(final LETTER symbol) {
		this(symbol, new ArrayList<>());
	}
	/**
	 * Construct a tree with root symbol, and children trees.
	 * @param symbol
	 * @param children
	 */
	public Tree(final LETTER symbol, final List<Tree<LETTER>> children) {
		this.children = new ArrayList<>();
		for (final Tree<LETTER> child : children) {
			if (child != null && child.symbol != null) {
				this.children.add(child);
			}
		}
		this.symbol = symbol;
	}
	
	public LETTER getSymbol() {
		return this.symbol;
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
