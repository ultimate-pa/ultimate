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
package de.uni_muenster.cs.sev.lethal.grammars.generic;

import de.uni_muenster.cs.sev.lethal.grammars.RTGRule;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;

/**
 * Simple generic implementation of a {@link RTGRule regular tree grammar rule}.
 * 
 * @param <F> type of symbols occurring in regular tree grammar rule
 * @param <Q> type of non-terminals occurring in regular tree grammar rule
 * 
 * @author Martin, Sezar
 */
public class GenRTGRule<F extends RankedSymbol, Q extends State> implements RTGRule<F,Q> {


	/** Left side of the regular tree grammar rule.*/
	private Q left;

	/** Right side of the regular tree grammar rule.*/
	private Tree<BiSymbol<F,Q>> right;

	/**
	 * Creates a new regular tree grammar rule with the supplied left and right sides.
	 * 
	 * @param left left side of the new regular tree grammar rule
	 * @param right right side of the new regular tree grammar rule
	 */
	public GenRTGRule(Q left, Tree<BiSymbol<F,Q>> right) {
		if (left == null)  throw new IllegalArgumentException("GenRTGRule(): left must not be null.");	
		if (right == null) throw new IllegalArgumentException("GenRTGRule(): right must not be null.");	
		this.left = left;
		this.right = right;
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.grammars.RTGRule#getLeftSide()
	 */
	@Override
	public Q getLeftSide() {
		return left;
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.grammars.RTGRule#getRightSide()
	 */
	@Override
	public Tree<BiSymbol<F, Q>> getRightSide() {
		return right;
	}

}
