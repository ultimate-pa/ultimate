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
package de.uni_muenster.cs.sev.lethal.grammars;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;

/**
 * Represents a regular tree grammar rule, which is of the form
 * A -> t, where A is a non-terminal symbol and t is a tree consisting of
 * non-terminal and terminal symbols.
 * 
 * @author Martin, Sezar
 *
 * @param <Q> type of non-terminal occurring on the left side and in the tree 
 * on the right side of the rule
 * @param <F> type of terminals which can occur on the right side of the rule
 */
public interface RTGRule<F extends RankedSymbol, Q extends State> {
	/**
	 * Returns the non-terminal symbol on the left side of the rule.
	 * 
	 * @return the non-terminal symbol on the left side of the rule
	 */
	Q getLeftSide();

	/**
	 * Returns the tree on the right side of the rule.
	 * 
	 * @return the tree on the right side of the rule
	 */
	Tree<BiSymbol<F,Q>> getRightSide();
}
