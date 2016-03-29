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
package de.uni_muenster.cs.sev.lethal.tree.standard;

import java.util.List;

import de.uni_muenster.cs.sev.lethal.symbol.common.Symbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.tree.common.TreeCreator;
import de.uni_muenster.cs.sev.lethal.factories.TreeFactory;


/**
 * Standard implementation of TreeCreator using the global factory.
 * 
 * @param <S> symbol type of trees to be created
 * 
 * @author Dorothea, Irene, Martin
 */
public class StdTreeCreator<S extends Symbol> implements TreeCreator<S,Tree<S>> {

	/**
	 * @see de.uni_muenster.cs.sev.lethal.tree.common.TreeCreator#makeTree(de.uni_muenster.cs.sev.lethal.symbol.common.Symbol, java.util.List)
	 */
	@Override
	public Tree<S> makeTree(S symbol, List<Tree<S>> subTrees) {
		return TreeFactory.getTreeFactory().makeTreeFromSymbol(symbol, subTrees);
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.tree.common.TreeCreator#makeTree(de.uni_muenster.cs.sev.lethal.symbol.common.Symbol)
	 */
	@Override
	public Tree<S> makeTree(S symbol) {
		return TreeFactory.getTreeFactory().makeTreeFromSymbol(symbol);
	}
}
