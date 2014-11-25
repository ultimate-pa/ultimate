/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;


/**
 * Contains methods which are shared by Acceptance and BuchiAcceptance.  
 * @author heizmann@informatik.uni-freiburg.de
 */
public abstract class AbstractAcceptance<LETTER,STATE> {
	
	private static Logger s_Logger = NestedWordAutomata.getLogger();
	
	
	/**
	 * Result contains a configuration for each state which contains only this
	 * state.
	 */
	public Set<Stack<STATE>> emptyStackConfiguration(Iterable<STATE> states) {
		Set<Stack<STATE>> configurations = new HashSet<Stack<STATE>>();
		for (STATE state : states) {
			Stack<STATE> singletonStack = new Stack<STATE>();
			singletonStack.push(state);
			configurations.add(singletonStack);
		}
		return configurations;
	}
	
	/**
	 * Returns true iff the topmost stack element is an accepting state.
	 */
	public boolean isAcceptingConfiguration(Stack<STATE> configuration,
			INestedWordAutomatonSimple<LETTER,STATE> nwa) {
			STATE state = configuration.peek();
			if (nwa.isFinal(state)) {
				return true;
			}
		return false;
	}
	

	/**
	 * Compute successor configurations for a set of given configurations and
	 * one letter of a nested word. A configuration is given as a stack of
	 * states. (topmost element: current state, other elements: states occurred
	 * on a run at call positions) If the letter is at an internal position we
	 * consider only internal successors. If the letter is at a call position we
	 * consider only call successors. If the letter is at a return position we
	 * consider only return successors and consider the second topmost stack
	 * element as hierarchical predecessor.
	 * 
	 * @param position
	 *            of the symbol in the nested word for which the successors are
	 *            computed.
	 * @param addInitial
	 *            if true we add for each initial state an stack that contains
	 *            only this initial state. Useful to check if suffix of word is
	 *            accepted. If set the input configurations is modified.
	 * 
	 */
	public Set<Stack<STATE>> successorConfigurations(Set<Stack<STATE>> configurations,
			NestedWord<LETTER> nw, int position, INestedWordAutomatonSimple<LETTER,STATE> nwa,
			boolean addInitial) {
		Set<Stack<STATE>> succConfigs = new HashSet<Stack<STATE>>();
		if (addInitial) {
			configurations.addAll(configurations);
		}
		for (Stack<STATE> config : configurations) {
			STATE state = config.pop();
			LETTER symbol = nw.getSymbol(position);
			if (nw.isInternalPosition(position)) {
				Iterable<OutgoingInternalTransition<LETTER, STATE>> outTransitions = 
						nwa.internalSuccessors(state, symbol);
				for (OutgoingInternalTransition<LETTER, STATE> outRans :outTransitions) {
					STATE succ = outRans.getSucc();
					Stack<STATE> succConfig = (Stack<STATE>) config.clone();
					succConfig.push(succ);
					succConfigs.add(succConfig);
				}
			} else if (nw.isCallPosition(position)) {
				Iterable<OutgoingCallTransition<LETTER, STATE>> outTransitions = 
						nwa.callSuccessors(state, symbol);
				for (OutgoingCallTransition<LETTER, STATE> outRans :outTransitions) {
					STATE succ = outRans.getSucc();
					Stack<STATE> succConfig = (Stack<STATE>) config.clone();
					succConfig.push(state);
					succConfig.push(succ);
					succConfigs.add(succConfig);
				}
			} else if (nw.isReturnPosition(position)) {
				if (config.isEmpty()) {
					s_Logger.warn("Input has pending returns, we reject such words");
				}
				else {
					STATE callPred = config.pop();
					Iterable<OutgoingReturnTransition<LETTER, STATE>> outTransitions = 
							nwa.returnSucccessors(state, callPred, symbol);
					for (OutgoingReturnTransition<LETTER, STATE> outRans :outTransitions) {
						STATE succ = outRans.getSucc();
						Stack<STATE> succConfig = (Stack<STATE>) config.clone();
						succConfig.push(succ);
						succConfigs.add(succConfig);
					}
					config.push(callPred);
				}
			} else {
				throw new AssertionError();
			}
			config.push(state);
		}
		return succConfigs;

	}
}
