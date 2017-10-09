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

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;


/**
 * (generalized) Buchi automata
 * */
public interface IBuchi<S extends IState> {
	
	Acc getAcceptance();
	
	int getStateSize();
	
	S addState();
	
	S makeState(int id);
	
	int addState(S state);
	
	S getState(int id);
	
	IntSet getInitialStates();

	IntSet getFinalStates();
	
	
	default public boolean isInitial(S s) {
		return isInitial(s.getId());
	}
	
	boolean isInitial(int id);
	
	default public boolean isFinal(S s) {
		return isFinal(s.getId());
	}
	
	boolean isFinal(int id);
	
	default public void setInitial(S s) {
		setInitial(s.getId());
	}
	
	void setInitial(int id);
	
	default public void setFinal(S s) {
		setFinal(s.getId());
	}
	
	void setFinal(int id);
	
	Collection<S> getStates();
	
	void makeComplete();
	
	int getAlphabetSize();
		
	int getTransitionSize();
	// printer
	
	default public String toDot() {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        try {
        	List<String> alphabet = new ArrayList<>();
        	for(int i = 0; i < getAlphabetSize(); i ++) {
        		alphabet.add(i + "");
        	}
            toDot(new PrintStream(out), alphabet);
            return out.toString();
        } catch (Exception e) {
            return "ERROR";
        }
	}
	
	default void toDot(PrintStream out, List<String> alphabet) {
		
		// output automata in dot
		out.print("digraph {\n");
		Collection<S> states = getStates();
		for(S state : states) {
			IntSet labels = getAcceptance().getLabels(state.getId());
//			out.print("  " + state.getId() + " [label=\"" +  state.getId() + "\"");
			out.print("  " + state.getId());
            if(isFinal(state.getId())) out.print(" [label=\"" +  state.getId() + "\"" + ", shape = doublecircle");
            else if(! labels.isEmpty()) {
            	out.print(" [label=\"" +  state.getId() + " " +  labels + "\"" + ", shape = box");
            }else out.print(", shape = circle");
            
            out.print("];\n");
            state.toDot(out, alphabet);
        }	
		out.print("  " + states.size() + " [label=\"\", shape = plaintext];\n");
        for(final Integer init : getInitialStates().iterable()) {
        	out.print("  " + states.size() + " -> " + init + " [label=\"\"];\n");
        }
        
        out.print("}\n\n");

	}
	
	void toATS(PrintStream out, List<String> alphabet);
	
	// a Buchi automaton is semideterministic 
	// if all transitions after the accepting states are deterministic
	boolean isSemiDeterministic();
	
	boolean isDeterministic(int state);

}
