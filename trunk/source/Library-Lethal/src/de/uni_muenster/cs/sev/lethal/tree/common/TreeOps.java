/*
 * Copyright 2009 Dorothea Jansen <d.jansen@uni-muenster.de>, Martin Mohr <mohrfrosch@uni-muenster.de>, Irene Thesing <i_thes01@uni-muenster.de>, Anton Reis <antonreis@gmx.de>, Maria Schatz <m_scha17@uni-muenster.de>, Philipp Claves <philipp.claves@uni-muenster.de>, Sezar Jarrous <sezar.jarrous@gmail.com>
 *
 * This file is part of LETHAL.
 *
 * LETHAL is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * LETHAL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with LETHAL.  If not, see <http://www.gnu.org/licenses/>.
 */
/**
 * 
 */
package de.uni_muenster.cs.sev.lethal.tree.common;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import de.uni_muenster.cs.sev.lethal.symbol.common.Symbol;
import de.uni_muenster.cs.sev.lethal.utils.Converter;


/**
 * Some standard operations on trees, like calculating the height or the contained symbols.
 * 
 * @author Dorothea, Irene, Martin
 */
public class TreeOps {

	/**
	 * Calculates the height of a tree, that is the maximal depth.
	 * 
	 * @param <S> type of symbols occurring in given tree
	 * @param tree tree of which the height shall be computed
	 * @return height of the tree
	 */
	public static <S extends Symbol> int getHeight(Tree<S> tree){
		int max = 0;
		for (Tree<S> sub: tree.getSubTrees()){
			int height = getHeight(sub);
			if (height > max)
				max = height;
		}
		return 1+max;
	}

	/**
	 * Collects all contained symbols in the tree.
	 * 
	 * @param <S> type of symbols occurring in given tree
	 * @param tree if which the set of all symbols shall be computed
	 * @return set of all symbols contained in the specified tree
	 */
	public static <S extends Symbol> Set<S> getAllContainedSymbols(Tree<S> tree){
		Set<S> symbols = new HashSet<S>();
		Stack<Tree<S>> toDo = new Stack<Tree<S>>();
		toDo.push(tree);
		while (!toDo.isEmpty()) {
			Tree<S> next = toDo.pop();
			symbols.add(next.getSymbol());
			for (Tree<S> sub: next.getSubTrees())
				toDo.push(sub);
		}
		return symbols;
	}

	/**
	 * Checks whether there is a subtree whose root is annotated with the specified symbol.
	 * 
	 * @param symbol symbol to be looked for
	 * @param tree tree in which the symbol shall be looked for
	 * @param <S> type of symbols occurring in given tree
	 * @return true if and only if there is a subtree whose root is annotated with the specified symbol
	 */
	public static <S extends Symbol> boolean containsSymbol(Tree<S> tree, S symbol){
		// true, if the root symbol is the looked for symbol
		if (tree.getSymbol().equals(symbol)) {
			return true;
			// else look in the subtrees
		} else {
			for (Tree<S> sub : tree.getSubTrees()){
				if (containsSymbol(sub, symbol)){
					return true;
				}
			}
		}
		// if we are at this point, the symbol is not contained
		return false;
	}

	/**
	 * Converts a tree with symbols of a certain type into a tree with symbols of another type
	 * using a given symbol converter.
	 * 
	 * @param <S1> type of symbols occurring in the given tree
	 * @param <S2> type of symbols occurring in the converted tree
	 * @param <T2> type of the converted tree
	 * @param tree tree to be converted
	 * @param c converter from symbols of type S1 into symbols of type S2 - conversion must be injective!
	 * @param tc tree creator object for creating the converted tree
	 * @return converted version of the given tree
	 */
	public static <S1 extends Symbol, 
	S2 extends Symbol, 
	T2 extends Tree<S2>> T2 convert(Tree<S1> tree, Converter<S1,S2> c, TreeCreator<S2,T2> tc) {
		S2 newSymbol = c.convert(tree.getSymbol());
		List<T2> newSubs = new LinkedList<T2>();
		for (Tree<S1> sub: tree.getSubTrees()) {
			newSubs.add(convert(sub,c,tc));
		}
		return tc.makeTree(newSymbol,newSubs);
	}
}
