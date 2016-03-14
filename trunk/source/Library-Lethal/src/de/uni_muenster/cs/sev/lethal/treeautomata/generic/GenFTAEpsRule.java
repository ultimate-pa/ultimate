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
package de.uni_muenster.cs.sev.lethal.treeautomata.generic;

import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAEpsRule;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAOps;

/**
 * Simple implementation of FTAEpsRule using generic types. <br>
 * It is used in several algorithms for
 * building finite tree automata with epsilon rules as
 * intermediate product, for example {@link FTAOps#substitute substitution} or 
 * {@link de.uni_muenster.cs.sev.lethal.hom.HomOps#applyOnAutomaton application of tree homomorphims} on finite tree automata.
 * 
 * @param <Q> type of states which this rule consists of
 * 
 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAEpsRule
 * 
 * @author Dorothea, Irene, Martin
 */
public class GenFTAEpsRule<Q> implements FTAEpsRule<Q>{

	/**
	 * The source state of this epsilon rule.
	 */
	private Q srcState;

	/**
	 * The destination state of this epsilon rule.
	 */
	private Q destState;

	/**
	 * Creates a new epsilon rule with given source and destination states.
	 * 
	 * @param src source state of the new epsilon rule
	 * @param dest destination state of the new epsilon rule
	 */
	public GenFTAEpsRule(Q src, Q dest){
		if (src == null || dest == null)
			throw new IllegalArgumentException("src and dest must not be null");
		srcState = src;
		destState = dest;
	}

	/**
	 * Returns the source state of the epsilon rule.
	 * 
	 * @return source state of the epsilon rule
	 */
	public Q getSrcState() {
		return srcState;
	}

	/**
	 * Returns the destination state of the epsilon rule.
	 * 
	 * @return destination state of the epsilon rule
	 */
	public Q getDestState() {
		return destState;
	}


	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString(){
		return srcState + "->" + destState;
	}

}
