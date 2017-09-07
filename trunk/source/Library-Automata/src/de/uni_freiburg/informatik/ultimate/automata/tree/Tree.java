/*
 * Copyright (C) 2016 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2014-2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.util.ArrayList;
import java.util.List;

/**
 * Class to create a tree for the tree automaton.
 * @author mostafa.amin93@gmail.com, grugelt@uni-freiburg.de
 * @param <LETTER> symbol
 */
public class Tree<LETTER extends IRankedLetter> {

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

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(symbol.toString());
		if (!getChildren().isEmpty()) {
			sb.append(getChildren().toString());
		}
		return sb.toString();
	}
	
 }
