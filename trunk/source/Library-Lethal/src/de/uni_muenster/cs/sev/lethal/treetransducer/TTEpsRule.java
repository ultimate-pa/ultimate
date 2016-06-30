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
import de.uni_muenster.cs.sev.lethal.tree.common.VarTreeOps;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAEpsRule;
import de.uni_muenster.cs.sev.lethal.utils.Pair;

/**
 * Represents an epsilon rule q1-> (q2,v) of a tree transducer,
 * where v is a tree containig variables with at most one variable. 
 * This variable has the number 0.
 *    
 * @param <G> type of symbols of the destination alphabet
 * @param <Q> type of used states
 * 
 * @author Dorothea, Irene, Martin
 */
public class TTEpsRule<G extends RankedSymbol, Q extends State> extends Pair<TTState<Q,G>,TTState<Q,G>> implements FTAEpsRule<TTState<Q,G>>{


	/**
	 * Constructs a new epsilon rule of a tree transducer. It has the
	 * form q1-> (q2,v), where v is a variable tree with at most one 
	 * variable. This variable has the number 0.
	 * 
	 * @param src source state
	 * @param dest destination state
	 * @param var variable tree with at most one variable
	 */
	public TTEpsRule(Q src, Q dest, Tree<BiSymbol<G,Variable>> var) {
		super(new TTState<Q,G>(src),new TTState<Q,G>(dest,var));
		if (VarTreeOps.getHighestVariableNumber(var) > 0)
			throw new IllegalArgumentException("Rule is not correct, variable tree must have at most one homomorphism variable with number 0.");
	}


	/**
	 * Constructs a new epsilon rule of a tree transducer out of two given 
	 * {@link TTState tree transducer states}.<br>
	 * The tree contained in the destination state must not be null and 
	 * must not contain any variable with a number greater than 0, otherwise
	 * an exception is thrown. 
	 * 
	 * @param q source state
	 * @param p destination state
	 */
	public TTEpsRule(TTState<Q, G> q, TTState<Q, G> p) {
		super(q,p);
		if (p.getVarTree() == null)
			throw new IllegalArgumentException("There must be a variable tree.");
		else if(VarTreeOps.getHighestVariableNumber(p.getVarTree()) > 0)
			throw new IllegalArgumentException("Rule is not correct, variable tree must have at most one homomorphism variable with number 0.");

	}


	/**
	 * Returns the destination state, i.e. the state on the right side
	 * of the rule.
	 * 
	 * @return destination state, i.e. the state on the right side
	 * of the rule
	 */
	public TTState<Q,G> getDestState(){
		return this.getSecond();
	}

	/**
	 * Returns the tree containing variables on the right side of the epsilon rule.
	 * In the variable tree the variable can be replaced by another tree.
	 * 
	 * @return destination variable tree, where you can replace on variable
	 */
	public Tree<BiSymbol<G,Variable>> getDestTree(){
		return this.getSecond().getVarTree();
	}

	/**
	 * Returns the source state, i.e. the left side of the tree transducer
	 * rule.
	 * 
	 * @return source state, i.e. the left side of the epsilon rule
	 */
	public Q getSrcAsQ(){
		return this.getFirst().getState();
	}

	/**
	 * Returns the destination state, so the state on the right side
	 * of the rule.
	 * 
	 * @return destination state
	 */
	public Q getDestStateAsQ(){
		return this.getSecond().getState();
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAEpsRule#getSrcState()
	 */
	@Override
	public TTState<Q, G> getSrcState() {
		return this.getFirst();
	}


}
