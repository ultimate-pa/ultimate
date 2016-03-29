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
package de.uni_muenster.cs.sev.lethal.treeautomata.common;

import java.util.AbstractSet;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;

/**
 * A class to save rules in different ways. <br>
 * It is used to save rules in the trivial way or an efficient way for the algorithms. 
 * 
 * @param <Q> state type used in the rules
 * @param <F> symbol type used in the rules
 * @param <R> rule type
 * 
 * @author Dorothea, Irene, Martin
 */
public abstract class FTARuleSet<F extends RankedSymbol, Q extends State, R extends FTARule<F,Q>> extends AbstractSet<R> {

	/**
	 * Returns all rules f(q1,...,qn) -> q with specified symbol f.
	 * 
	 * @param f symbol which is to occur in the rules to return
	 * @return all rules f(q1,...,qn) -> with specified symbol f
	 */
	public abstract Set<R> getSymbolRules(F f);
}
