/*
 * Copyright (C) 2017 Yong Li (liyong@ios.ac.cn)
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


package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata;

import java.io.PrintStream;
import java.util.Collection;
import java.util.LinkedList;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntIterator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;

/**
 * @author Yong Li (liyong@ios.ac.cn)
 * */

public interface IBuchi {
	
	Acc getAcceptance();
	
	int getAlphabetSize();
	
	int getStateSize();
	
	IState addState();
	
	int addState(IState state);
	
	IState getState(int id);
	
	IntSet getInitialStates();

	IntSet getFinalStates();
	
	IState makeState(int id);
	
	
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
	
	default public IntSet getSuccessors(IntSet states, int letter) {
		IntSet result = UtilIntSet.newIntSet();
		IntIterator iter = states.iterator();
		while(iter.hasNext()) {
			int n = iter.next();
			result.or(getSuccessors(n, letter));
		}
		return result;
	}
	
	IntSet getSuccessors(int state, int letter);
	
	Collection<IState> getStates();
	
	void makeComplete();
	
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
            	IntSet succs = state.getSuccessors(letter);
        		IntIterator iter = succs.iterator();
        		while(iter.hasNext()) {
        			int succ = iter.next();
        			sb.append("  " + state.getId() + " -> " + succ + " [label=\"" + letter + "\"];\n");
        		}
            }
        }	
        sb.append("  " + states.size() + " [label=\"\", shape = plaintext];\n");
        IntSet initialStates = getInitialStates();
        IntIterator iter = initialStates.iterator();
        while(iter.hasNext()) {
        	int init = iter.next();
        	sb.append("  " + states.size() + " -> " + init + " [label=\"\"];\n");
        }
        
        sb.append("}\n\n");
		return sb.toString();
	}
	
	// RABIT format
	default public String toBA() {
		
		StringBuilder sb = new StringBuilder();
        IntSet initialStates = getInitialStates();
        if(initialStates.cardinality() > 1) 
        	throw new RuntimeException("BA format does not allow multiple initial states...");
        IntIterator iter = initialStates.iterator();
        sb.append("[" + iter.next() + "]\n");
		// output automata in BA (RABIT format)
		Collection<IState> states = getStates();
		for(IState state : states) {
            for (int letter = 0; letter < getAlphabetSize(); letter ++) {
            	IntSet succs = state.getSuccessors(letter);
            	iter = succs.iterator();
            	while(iter.hasNext()) {
            		int succ = iter.next();
            		sb.append("a" + letter + ",[" + state.getId() + "]->[" + succ + "]\n");
            	}
            }
        }	
        IntSet finStates = getFinalStates();
        iter = finStates.iterator();
        while(iter.hasNext()) {
        	sb.append("[" + iter.next() + "]\n");
        }
        
		return sb.toString();
	}
	
	// use this function if automtaton is too large 
	default public void toBA(PrintStream out) {
        IntSet initialStates = getInitialStates();
        if(initialStates.cardinality() > 1) 
        	throw new RuntimeException("BA format does not allow multiple initial states...");
        IntIterator iter = initialStates.iterator();
        out.print("[" + iter.next() + "]\n");
		// output automata in BA (RABIT format)
		Collection<IState> states = getStates();
		for(IState state : states) {
            for (int letter = 0; letter < getAlphabetSize(); letter ++) {
            	IntSet succs = state.getSuccessors(letter);
            	iter = succs.iterator();
            	while(iter.hasNext()) {
            		int succ = iter.next();
            		out.print("a" + letter + ",[" + state.getId() + "]->[" + succ + "]\n");
            	}
            }
        }	
        IntSet finStates = getFinalStates();
        iter = finStates.iterator();
        while(iter.hasNext()) {
        	out.print("[" + iter.next() + "]\n");
        }
	}
	
	default int getNumTransition() {
		int num = 0;
		for(IState s : getStates()) {
			for(Integer letter : s.getEnabledLetters()) {
				num += s.getSuccessors(letter).cardinality();
			}
		}
		return num;
	}
	
	// a Buchi automaton is semideterministic if all transitions after the accepting states are deterministic
	default boolean isSemiDeterministic() {
		IntSet finIds = getFinalStates();
		LinkedList<IState> walkList = new LinkedList<>();
		
		// add to list
		IntIterator iter = finIds.iterator();
		while(iter.hasNext()) {
			walkList.addFirst(getState(iter.next()));
		}
		
        IntSet visited = UtilIntSet.newIntSet();
        while(! walkList.isEmpty()) {
        	IState s = walkList.remove();
        	if(visited.get(s.getId())) continue;
        	visited.set(s.getId());
        	for(int i = 0; i < getAlphabetSize(); i ++) {
        		IntSet succs = s.getSuccessors(i);
        		if(succs.isEmpty()) continue;
        		if(succs.cardinality() > 1) return false;

        		iter = succs.iterator();
        		int succ = iter.next();
    			if(! visited.get(succ)) {
    				walkList.addFirst(getState(succ));
    			}
        	}
        }
        
        return true;
	}
	
	default boolean isDeterministic(int state) {
		LinkedList<IState> walkList = new LinkedList<>();
		
		walkList.addFirst(getState(state));
		
        IntSet visited = UtilIntSet.newIntSet();
        while(! walkList.isEmpty()) {
        	IState s = walkList.remove();
        	if(visited.get(s.getId())) continue;
        	visited.set(s.getId());
        	for(int i = 0; i < getAlphabetSize(); i ++) {
        		IntSet succs = s.getSuccessors(i);
        		if(succs.cardinality() > 1) return false;
        		if(succs.isEmpty()) continue;
        		IntIterator iter = succs.iterator();
        		int succ = iter.next();
    			if(! visited.get(succ)) {
    				walkList.addFirst(getState(succ));
    			}
        	}
        }
        
        return true;
	}


}
