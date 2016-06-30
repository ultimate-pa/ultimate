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
package de.uni_muenster.cs.sev.lethal.tree.special;

import java.util.ArrayList;
import java.util.List;

import de.uni_muenster.cs.sev.lethal.symbol.common.Symbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.standard.StdNamedRankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.standard.StdNamedUnrankedSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.tree.standard.StdAbstractTree;
import de.uni_muenster.cs.sev.lethal.factories.TreeFactory;

/**
 * Specialized tree class for representing a String as a Tree where each character of the string is a leaf node.
 * The tree has height 1 and the root node is labeled _string_.
 * This class allows for easy inclusion of string data into trees/hedges in a way 
 * that can be processed by tree/hedge automata.
 * 
 * @param <S> symbol type 
 * 
 * @see #StringTree
 *
 * @author Philipp
 */
public class StringTree<S extends Symbol> extends StdAbstractTree<S> implements Tree<S> {

	private Class<? extends S> symClass;
	private final S rootSymbol;
	private String string;
	private List<? extends Tree<S>> subtrees = null; 

	/**
	 * Creates a new StringTree instance.
	 * @param symClass Base class of the symbol.
	 *        Valid values are UnrankedSymbol (for use in hedges) and RankedSymbol (for use in ranked trees).
	 *        Other values are only valid if they are explicitly registered in the NamedSymbolTreeFactory
	 *        and compatible with either StdNamedUnrankedSymbol or StdNamedRankedSymbol.
	 * @param s string represented by this tree
	 */
	@SuppressWarnings("unchecked")
	public StringTree(Class<? extends S> symClass, String s){
		super();
		this.string = s;
		this.symClass = symClass;
		if (UnrankedSymbol.class.isAssignableFrom(symClass)) {
			this.rootSymbol = (S) new StdNamedUnrankedSymbol<String>("_string_");
		} else {
			this.rootSymbol = (S) new StdNamedRankedSymbol<String>("_string_", s.length());
		}
	}


	@Override
	public List<? extends Tree<S>> getSubTrees() {
		if (this.subtrees == null) this.subtrees = createSymbolList();
		return this.subtrees;
	}


	@Override
	public S getSymbol() {
		return this.rootSymbol;
	}


	@Override
	public Class<? extends Symbol> getSymbolClass() {
		return this.rootSymbol.getClass();
	}


	private List<? extends Tree<S>> createSymbolList(){
		List<Tree<S>> subtrees = new ArrayList<Tree<S>>(this.string.length());
		for (int i = 0; i < this.string.length(); i++){
			subtrees.add(TreeFactory.<S>getTreeFactory(symClass).makeTreeFromName(this.string.substring(i,i+1)));
		}
		return subtrees;
	}


	@Override
	protected int calcHashCode() {
		return (31 * this.rootSymbol.hashCode()) + this.string.hashCode();
	}


	@Override
	public boolean equals(Object t) {
		if (t instanceof StringTree<?>){
			return this.rootSymbol.equals(((StringTree<?>) t).getSymbol()) && this.string.equals(((StringTree<?>) t).string);
		} else {
			return super.equals(t);
		}
	}


	@Override
	public String toString() {
		return "\"" + this.string + "\"" ;
	}

}
