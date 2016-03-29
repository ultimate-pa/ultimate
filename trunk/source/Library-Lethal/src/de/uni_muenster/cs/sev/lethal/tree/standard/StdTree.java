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
package de.uni_muenster.cs.sev.lethal.tree.standard;

import java.util.Collections;
import java.util.List;

import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.Symbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;


/**
 * Standard implementation of a tree or hedge structure, which stores the root symbol and the subtrees 
 * as protected attributes.
 *   
 * @param <S> tree node symbol type
 * @author Anton, Dorothea, Irene, Maria, Martin, Philipp, Sezar
 */
public class StdTree<S extends Symbol> extends StdAbstractTree<S> implements Tree<S> {

	/**
	 * Root symbol of the tree.
	 */
	protected S symbol;


	/**
	 * Subtrees.
	 */
	protected List<? extends Tree<S>> subtrees;


	/**
	 * Constructs a new StdTree which uses the given symbol as root symbol and the given trees
	 * as subtrees.
	 * 
	 * @param symbol the symbol which is to be used as root symbol of the tree to be constructed
	 * @param subtrees a list of trees which are to be used as subtrees of the tree to be constructed
	 */
	public StdTree(S symbol, List<? extends Tree<S>> subtrees){
		super();
		if (symbol == null)   throw new IllegalArgumentException("StdTree(): symbol must not be null.");
		if (subtrees == null) throw new IllegalArgumentException("StdTree(): subtrees must not be null. For a leaf us an empty list or the symbol only constructor.");
		if (symbol instanceof RankedSymbol && !(((RankedSymbol)symbol).getArity() == subtrees.size())) throw new IllegalArgumentException("Ranked symbol arity does not match the number of subtrees");

		this.symbol = symbol;
		this.subtrees = subtrees;
	}


	/**
	 * Constructs a new StdTree which has the given symbol as root symbol and no
	 * subtrees, using {@link Collections#emptyList}.
	 * 
	 * @param symbol the symbol which is to be used as root symbol of the tree to be constructed
	 */
	public StdTree(S symbol) {
		if (symbol == null)   throw new IllegalArgumentException("StdTree(): symbol must not be null.");
		this.symbol = symbol;
		this.subtrees = Collections.<Tree<S>>emptyList();
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.tree.common.Tree#getSubTrees()
	 */
	@Override
	public List<? extends Tree<S>> getSubTrees() {
		return this.subtrees;
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.tree.common.Tree#getSymbol()
	 */
	@Override
	public S getSymbol() {
		return this.symbol;
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.tree.common.Tree#getSymbolClass()
	 */
	@Override
	public Class<? extends Symbol> getSymbolClass() {
		return this.symbol.getClass();
	}

}