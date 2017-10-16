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
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;



/**
 * Buchi nested word automata 
 * */
public interface IBuchiNwa extends IBuchi<IStateNwa> {
	
	IntSet getAlphabetInternal();
	
	IntSet getAlphabetCall();
	
	IntSet getAlphabetReturn();
	
	// get nested alphabet size
	default public int getAlphabetSize() {
		return getAlphabetInternal().cardinality() + getAlphabetCall().cardinality() + getAlphabetReturn().cardinality();
	}
	
	// should use functional programming to following three 
	default public IntSet getSuccessorsInternal(IntSet states, int letter) {
		assert getAlphabetInternal().get(letter);
		IntSet result = UtilIntSet.newIntSet();
		for(final Integer state : states.iterable()) {
			result.or(getSuccessorsInternal(state, letter));
		}
		return result;
	}
	
	default public IntSet getSuccessorsCall(IntSet states, int letter) {
		assert getAlphabetCall().get(letter);
		IntSet result = UtilIntSet.newIntSet();
		for(final Integer state : states.iterable()) {
			result.or(getSuccessorsCall(state, letter));
		}
		return result;
	}
	
	default public IntSet getSuccessorsReturn(IntSet states, int letter) {
		assert getAlphabetReturn().get(letter);
		IntSet result = UtilIntSet.newIntSet();
		for(final Integer state : states.iterable()) {
			Set<Integer> enabledHiers = getState(state).getEnabledHiersReturn(letter);
			for(Integer hier : enabledHiers) {
				result.or(getState(state).getSuccessorsReturn(hier, letter));
			}
		}
		return result;
	}
	
	IntSet getSuccessorsInternal(int state, int letter);

	IntSet getSuccessorsCall(int state, int letter);

	IntSet getSuccessorsReturn(int state, int hier, int letter);	
	
	default public void toATS(PrintStream out, List<String> alphabet) {
		final String PRE_BLANK = "   "; 
		final String ITEM_BLANK = " ";
		final String LINE_END = "},";
		final String BLOCK_END = "\n" + PRE_BLANK + "},";
		final String TRANS_PRE_BLANK = PRE_BLANK + "   "; 
		out.println("NestedWordAutomaton result = (");
        
        out.print(PRE_BLANK + "callAlphabet = {");
        for(final Integer id : getAlphabetCall().iterable()) {
        	out.print(alphabet.get(id) + ITEM_BLANK);
        }
        out.println(LINE_END);
        
        out.print(PRE_BLANK + "internalAlphabet = {");
        for(final Integer id : getAlphabetInternal().iterable()) {
        	out.print(alphabet.get(id) + ITEM_BLANK);
        }
        out.println(LINE_END);
        
        out.print(PRE_BLANK + "returnAlphabet = {");
        for(final Integer id : getAlphabetReturn().iterable()) {
        	out.print(alphabet.get(id) + ITEM_BLANK);
        }
        out.println(LINE_END);
        
        // states
		Collection<IStateNwa> states = getStates();
		out.print(PRE_BLANK + "states = {");
		for(IStateNwa state : states) {
			out.print("s" + state.getId() + ITEM_BLANK);
        }	
        out.println(LINE_END);
        // initial states
        out.print(PRE_BLANK + "initialStates = {");
        for(final Integer id : getInitialStates().iterable()) {
        	out.print("s" + id + ITEM_BLANK);
        }
        out.println(LINE_END);
        
        // final states
        out.print(PRE_BLANK + "finalStates = {");
        for(final Integer id : getFinalStates().iterable()) {
        	out.print("s" + id + ITEM_BLANK);
        }
        out.println(LINE_END);
        
        // call transitions
        out.print(PRE_BLANK + "callTransitions = {");
		for(IStateNwa state : states) {
			for(final Integer letter : state.getEnabledLettersCall()) {
            	for(final Integer succ : state.getSuccessorsCall(letter).iterable()) {
            		out.print("\n" + TRANS_PRE_BLANK + "(s" + state.getId() + " " + alphabet.get(letter) + " s" + succ + ")" );
            	}
            }
        }
		out.println(BLOCK_END);
        
        // internal transitions
        out.print(PRE_BLANK + "internalTransitions = {");
		for(IStateNwa state : states) {
			for(final Integer letter : state.getEnabledLettersInternal()) {
            	for(final Integer succ : state.getSuccessorsInternal(letter).iterable()) {
            		out.print("\n" + TRANS_PRE_BLANK + "(s" + state.getId() + " " + alphabet.get(letter) + " s" + succ + ")" );
            	}
            }
        }
		out.println(BLOCK_END);
		
        // return transitions
        out.print(PRE_BLANK + "returnTransitions = {");
		for(IStateNwa state : states) {
			for(final Integer letter : state.getEnabledLettersReturn()) {
            	Set<Integer> enabledHiers = state.getEnabledHiersReturn(letter);
            	for(Integer hier : enabledHiers) {
            		if(hier < 0) continue;
                	for(Integer succ : state.getSuccessorsReturn(hier, letter).iterable()) {
                		out.print("\n" + TRANS_PRE_BLANK + "(s" + state.getId() + " s" + hier + " " + alphabet.get(letter) + " s" + succ + ")" );
                	}
            	}
            }
        }
		out.println("\n" + PRE_BLANK + "}");
		
		out.println(");");
	}
	
	
	default int getTransitionSize() {
		int num = 0;
		for(IStateNwa s : getStates()) {
			// call 
			for(Integer letter : s.getEnabledLettersCall()) {
				num += s.getSuccessorsCall(letter).cardinality();
			}
			// internal 
			for(Integer letter : s.getEnabledLettersInternal()) {
				num += s.getSuccessorsInternal(letter).cardinality();
			}
			// return 
			for(Integer letter : s.getEnabledLettersReturn()) {
				for(Integer hier : s.getEnabledHiersReturn(letter)) {
					num += s.getSuccessorsReturn(hier, letter).cardinality();	
				}
			}
		}
		return num;
	}
	
	@Override
	default public void makeComplete() {
		throw new UnsupportedOperationException("unsupported function in nested word automata");
	}

	@Override
	default public boolean isSemiDeterministic() {
		throw new UnsupportedOperationException("unsupported function in nested word automata");
	}

	@Override
	default public boolean isDeterministic(int state) {
		throw new UnsupportedOperationException("unsupported function in nested word automata");
	}
	
	

}
