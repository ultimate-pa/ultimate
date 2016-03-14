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
package de.uni_muenster.cs.sev.lethal.factories;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Random;

import de.uni_muenster.cs.sev.lethal.symbol.common.Symbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;

/**
 * The NamedSymbolTreeFactory can create trees with named symbol sub-types from a symbol name and subtrees. <br>
 * Currently the creation of UnrankedSymbol and RankedSymbol trees is supported. The returned objects
 * are instances of StdNamedUnrankedSymbol and StdNamedRankedSymbol respectively.
 * 
 * @author Philipp
 * @param <S> type of the symbol to create
 */
public abstract class NamedSymbolTreeFactory<S extends Symbol> extends StdTreeFactory{

	private Class<S> symClass;
	
	private Random rnd = new Random();

	/**
	 * Constructor for the NamedSymbolTreeFactory.
	 * @param symClass symbol class to create. Currently creation of 
	 * UnrankedSymbol and RankedSymbol trees is supported.
	 * The returned objects are instances of StdNamedUnrankedSymbol and StdNamedRankedSymbol respectively.
	 */
	public NamedSymbolTreeFactory(Class<S> symClass){
		this.symClass = symClass;
	}
	
	/**
	 * Creates a tree with a named symbol from the given name and subclass. <br>
	 * Note that because of type system limitations the return type of the method is not completely accurate.
	 * The symbol of the resulting tree can be safely casted to NamedSymbol<T>. <br>
	 * Important: Alternate/derived implementations of this class must ensure this.
	 * @param <T> type of the name of the symbol in the root of the resulting tree
	 * @param name the name of the symbol in the root of the resulting tree
	 * @param subtrees subtrees of the tree to create
	 * @return the created tree
	 */
	public <T> Tree<S> makeTreeFromName(T name, List<? extends Tree<S>> subtrees){
		return super.makeTreeFromSymbol(makeSymbol(name, subtrees), subtrees);
	}

	/**
	 * Creates a leaf tree (no subtrees) with a named symbol from the given name and subclass.<br>
	 * Note that because of type system limitations the return type of the method isn't completely accurate.
	 * The symbol of the resulting tree can be safely casted to NamedSymbol<T>.<br>
	 * Important: Alternate/derived implementations of this class must ensure this.
	 * @param <T> type of the name of the symbol in the root of the resulting tree
	 * @param name the name of the symbol in the root of the resulting tree
	 * @return the created tree
	 */
	public <T> Tree<S> makeTreeFromName(T name){
		return super.makeTreeFromSymbol(makeSymbol(name, Collections.<Tree<S>>emptyList() ), Collections.<Tree<S>>emptyList() );
	}

	/**
	 * Creates a symbol from a given name, to be implemented by subclass.
	 * @param <T> type of the name in the symbol
	 * @param name name of the symbol
	 * @param subtrees subtrees of the tree where this symbol will be the root of
	 * @return the created root symbol
	 */
	protected abstract <T> S makeSymbol(T name, List<? extends Tree<S>> subtrees);

	/**
	 * Generates a random tree with the given size restrictions.
	 * @param maxHeight maximum height (length of longest path from root to a leaf) of the tree
	 * @param minWidth minimum width (number of leaf nodes) of the tree
	 * @param maxWidth minimum width (number of leaf nodes) of the tree
	 * @return the generated tree
	 */
	public Tree<S> generateRandomTree(int maxHeight, int minWidth, int maxWidth){
		return generateRandomTree(maxHeight,minWidth, maxWidth, null);
	}
	
	/**
	 * Generates a random tree with the given size restrictions.
	 * @param maxHeight maximum height (length of longest path from root to a leaf) of the tree
	 * @param minWidth minimum width (number of leaf nodes) of the tree
	 * @param maxWidth minimum width (number of leaf nodes) of the tree
	 * @param symbolNames a list of names for the symbols in the generated tree.
	 * @return the generated tree.
	 */
	public Tree<S> generateRandomTree(int maxHeight, int minWidth, int maxWidth, List<Object> symbolNames){
		List<Tree<S>> subtrees = new ArrayList<Tree<S>>(maxWidth);
		int bottomLeafs = minWidth + ((maxHeight > 3) ? 0 : rnd.nextInt(maxWidth - minWidth + 1));
		int curWidth = bottomLeafs;
		for (int i = 0; i < bottomLeafs; i++){ //generate the leafes at the very bottom of the tree
			subtrees.add(this.makeTreeFromName(randomSymbolName(symbolNames)));
		}
		for (int i = 0; i < (maxHeight - 2); i++){ //Iterate the levels of the tree (the last one, outside this loop, will just be grouping together all remaining subtrees).
			List<Tree<S>> newSubtrees = new ArrayList<Tree<S>>(subtrees.size());
			int[] borders = new int[subtrees.size()];
			//generate a random list of borders between the subtrees.
			for (int j = 0; j < (subtrees.size() - 1); j++) borders[j] = rnd.nextInt(subtrees.size());
			borders[subtrees.size() - 1] = subtrees.size(); //last border is number of subtrees
			Arrays.sort(borders);
			
			int lowerBorder = 0;
			for (int upperBorder : borders){ //iterate the borders and group subtrees together.
				List<Tree<S>> newTreeSubtrees = new ArrayList<Tree<S>>();
				if (upperBorder == lowerBorder) continue; //skip zero length intervals
				
				for (Tree<S> subtree : subtrees.subList(lowerBorder, upperBorder)){ //iterate all subtrees of the new tree
					//random insertion of new leaf nodes above the bottom level. Increase probability with each level, because the number of subtrees decreases
					int newLeafs = rnd.nextInt((i * (maxWidth - curWidth)) /maxHeight + 1);
					for (int j = 0; j < newLeafs; j++) newTreeSubtrees.add(this.makeTreeFromName(randomSymbolName(symbolNames)));
					curWidth += newLeafs;
					
					newTreeSubtrees.add(subtree); //add to the subtrees of the new tree
					
				}
				//random insertion of new leaf nodes above the bottom level. Increase probability with each level, because the number of subtrees decreases
				int newLeafs = rnd.nextInt((i * (maxWidth - curWidth)) /maxHeight + 1);
				for (int j = 0; j < newLeafs; j++) newTreeSubtrees.add(this.makeTreeFromName(randomSymbolName(symbolNames)));
				curWidth += newLeafs;
				
				Tree<S> newTree = this.makeTreeFromName(randomSymbolName(symbolNames), newTreeSubtrees);
				newSubtrees.add(newTree); //add the new created tree
				
				lowerBorder = upperBorder;
			}
			subtrees = newSubtrees;
			
			if (subtrees.size() == 1) break; //break if there is only one tree left.
		}
		
		if (subtrees.size() > 1){
			return this.makeTreeFromName(randomSymbolName(symbolNames), subtrees);
		} else {
			return subtrees.get(0);
		}
	}
	
	private Object randomSymbolName(List<Object> symbolNames){
		if (symbolNames != null){
			return symbolNames.get(rnd.nextInt(symbolNames.size()));
		} else {
			return String.valueOf((char)('a' + rnd.nextInt('z' - 'a' + 1)));
		}
	}
	
	/**
	 * Returns the class of the symbol created by this NamedSymbolTreeFactory.
	 * @return the class of the symbol created by this NamedSymbolTreeFactory
	 */
	public Class<S> getSymbolClass(){
		return this.symClass;
	}
}
