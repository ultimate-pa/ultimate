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

import de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.Symbol;
import de.uni_muenster.cs.sev.lethal.symbol.standard.InnerSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.standard.LeafSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;


/**
 * Standard implementation of tree structures with two kinds of symbols,
 * which stores the root symbol and the subtrees in a list.
 *
 * @param <I> type of symbols which can be used for leaves or inner nodes
 * @param <L> type of symbols which must be used as leaves
 *  
 * @author Martin
 */
public class StdBiTree<I extends Symbol,L> extends StdTree<BiSymbol<I,L>>{

	/**
	 * Creates a BiTree out of a leaf.
	 * 
	 * @param leaf leaf to be put into a tree
	 */
	public StdBiTree(final L leaf) {
		super(new LeafSymbol<I,L>(leaf), Collections.<Tree<BiSymbol<I,L>>>emptyList());
	}

	/**
	 * Creates a BiTree out of a root symbol and subtrees.
	 * 
	 * @param symbol root symbol of the new bitree
	 * @param subTrees subtrees of the new bitree 
	 */
	public StdBiTree(final I symbol, List<? extends Tree<BiSymbol<I,L>>> subTrees) {
		super(new InnerSymbol<I,L>(symbol), subTrees);
	}
}
