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
package de.uni_muenster.cs.sev.lethal.treetransducer;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.Variable;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;

/**
 * Represents an epsilon rule q1-> (q2,v) of a tree transducer,
 * where v is a homomorphism variable tree with at most one variable. 
 * The variable has the number 0.
 * 
 * @author Dorothea, Irene, Martin
 */
public class EasyTTEpsRule extends TTEpsRule<RankedSymbol,State>{


	/**
	 * Constructs a new epsilon rule of a tree transducer. It has the
	 * form q1-> (q2,v), where v is a variable tree with at most one 
	 * variable with number 0, out of two states and a variable tree.
	 * 
	 * @param src source state
	 * @param dest destination state
	 * @param var variable tree with at most one variable. The variable has the number 0.
	 */
	/*public EasyTTEpsRule(State src, State dest, StdBiTree<RankedSymbol,Variable> var) {
		super(src,dest,var);
	}*/
	
	/**
	 * Constructs a new epsilon rule of a tree transducer. It has the
	 * form q1-> (q2,v), where v is a variable tree with at most one 
	 * variable with number 0, out of two states and a variable tree.
	 * 
	 * @param src source state
	 * @param dest destination state
	 * @param var variable tree with at most one variable. The variable has the number 0.
	 */
	public EasyTTEpsRule(State src, State dest, Tree<BiSymbol<RankedSymbol,Variable>> var) {
		super(src,dest,var);
	}


}
