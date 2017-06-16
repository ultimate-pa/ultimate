/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */


package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.antichain;

import java.util.BitSet;
import java.util.Collection;



/**
 * @author Yong Li (liyong@ios.ac.cn)
 * */
public interface IBuchi {
	
	int getAlphabetSize();
	
	int getStateSize();
	
	IState addState();
	
	int addState(IState state);
	
	IState getState(int id);
	
	BitSet getInitialStates();

	BitSet getFinalStates();
	
	default public boolean isInitial(IState s) {
		return isInitial(s.getId());
	}
	
	boolean isInitial(int id);
	
	default public boolean isFinal(IState s) {
		return isFinal(s.getId());
	}
	
	boolean isFinal(int id);
	
	default public void setInitial(IState s) {
		setInitial(s.getId());
	}
	
	void setInitial(int id);
	
	default public void setFinal(IState s) {
		setFinal(s.getId());
	}
	
	void setFinal(int id);
	
	
	default public BitSet getSuccessors(BitSet states, int letter) {
		BitSet result = new BitSet();
		for(int n = states.nextSetBit(0); n >= 0; n = states.nextSetBit(n + 1)) {
			result.or(getSuccessors(n, letter));
		}
		return result;
	}
	
	BitSet getSuccessors(int state, int letter);
	
	Collection<IState> getStates();
	
	default public String toDot() {
		
		StringBuilder sb = new StringBuilder();
		
		// output automata in dot
		sb.append("digraph {\n");
		Collection<IState> states = getStates();
		for(IState state : states) {
			sb.append("  " + state.getId() + " [label=\"" +  state.getId() + "\"");
            if(isFinal(state.getId())) sb.append(", shape = doublecircle");
            else sb.append(", shape = circle");
            sb.append("];\n");
            for (int letter = 0; letter < getAlphabetSize(); letter ++) {
            	BitSet succs = state.getSuccessors(letter);
            	for(int succ = succs.nextSetBit(0); succ >= 0; succ = succs.nextSetBit(succ + 1)) {
            		sb.append("  " + state.getId() + " -> " + succ + " [label=\"" + letter + "\"];\n");
            	}
            }
        }	
        sb.append("  " + states.size() + " [label=\"\", shape = plaintext];\n");
        BitSet initialStates = getInitialStates();
        for(int init = initialStates.nextSetBit(0); init >= 0; init = initialStates.nextSetBit(init + 1)) {
        	sb.append("  " + states.size() + " -> " + init + " [label=\"\"];\n");
        }
        
        sb.append("}\n\n");
		return sb.toString();
	}
	
	default public String toBA() {
		
		StringBuilder sb = new StringBuilder();
		
		// output automata in dot
		Collection<IState> states = getStates();
		BitSet inits = this.getInitialStates();
		for(int i = inits.nextSetBit(0); i >= 0; i = inits.nextSetBit(i + 1)) {
			sb.append("s" + i + "\n");
		}
		for(IState state : states) {
            for (int letter = 0; letter < getAlphabetSize(); letter ++) {
            	BitSet succs = state.getSuccessors(letter);
            	for(int succ = succs.nextSetBit(0); succ >= 0; succ = succs.nextSetBit(succ + 1)) {
            		sb.append("a"+ letter + ",s" + state.getId() + "->s" + succ + "\n");
            	}
            }
        }	

		BitSet finals = this.getFinalStates();
        for(int j = finals.nextSetBit(0); j >= 0; j = finals.nextSetBit(j + 1)) {
        	sb.append("s" + j + "\n");
        }
 
		return sb.toString();
	}


}
