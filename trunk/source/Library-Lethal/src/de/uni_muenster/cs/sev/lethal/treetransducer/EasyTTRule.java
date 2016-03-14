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
package de.uni_muenster.cs.sev.lethal.treetransducer;

import java.util.Arrays;
import java.util.List;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.Variable;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.tree.standard.StdBiTree;


/**
 * Represents a rule for a tree transducer, which has the form
 * f(q1,...qn) -> (q,u), where f is a ranked symbol, q1, ...,qn,q are states 
 * and u is a variable tree with at most n different variables.
 *  
 * @see EasyTT
 * @see TTEpsRule
 * @see TTRuleSet
 * 
 * @author Dorothea, Irene, Martin
 */
public class EasyTTRule extends TTRule<RankedSymbol,RankedSymbol,State>{

	/**
	 * Constructs a new EasyTTRule of the form f(q1,...qn) -> (q,u), 
	 * where f is a ranked symbol, q1,...,qn, q are states and u is a 
	 * variable tree with at most n different variables.
	 * 
	 * @param s symbol of the rule
	 * @param src list of source states of the rule
	 * @param q destination state of the rule
	 * @param tree destination tree of the rule, variable tree with at most n different variables, i.e. 
	 * the highest number of a variable is arity(s)-1.
	 */
/*	public EasyTTRule(RankedSymbol s, List<State> src, State q, StdBiTree<RankedSymbol,Variable> tree){
		super(s,src,q,tree);
	}*/
	
	/**
	 * Constructs a new EasyTTRule in the form f(q1,...qn) -> (q,u), 
	 * where f is a ranked symbol, q1,...,qn, q are states and u is a 
	 * variable tree with at most n different variables.
	 * 
	 * @param s symbol of the rule
	 * @param src list of source states of the rule
	 * @param q destination state of the rule
	 * @param tree destination tree of the rule, variable tree with at most n different variables, i.e. 
	 * the highest number of a variable is arity(s)-1.
	 */
	public EasyTTRule(RankedSymbol s, List<State> src, State q, Tree<BiSymbol<RankedSymbol,Variable>> tree){
		super(s,src,q,tree);
	}

	/**
	 * Constructs a new EasyTTRule of the form f(q1,...qn) -> (q,u), 
	 * where f is a ranked symbol, q1,...,qn, q are states and u is a 
	 * variable tree with at most n different variable.<br> 
	 * Constructur with vararg-notation.
	 * 
	 * @param s function symbol of the rule
	 * @param tree destination tree of the rule
	 * @param q destination state of the rule
	 * @param src source states of the rule
	 */
	public EasyTTRule(RankedSymbol s, State q, StdBiTree<RankedSymbol,Variable> tree, State... src){
		super(s,Arrays.asList(src),q,tree);
	}

}
