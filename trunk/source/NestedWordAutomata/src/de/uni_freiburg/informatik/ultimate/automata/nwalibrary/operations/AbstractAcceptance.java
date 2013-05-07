package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;


/**
 * Contains methods which are shared by Acceptance and BuchiAcceptance.  
 * @author heizmann@informatik.uni-freiburg.de
 */
public abstract class AbstractAcceptance<LETTER,STATE> {
	
	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);
	
	
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
			INestedWordAutomaton<LETTER,STATE> nwa) {
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
			NestedWord<LETTER> nw, int position, INestedWordAutomaton<LETTER,STATE> nwa,
			boolean addInitial) {
		Set<Stack<STATE>> succConfigs = new HashSet<Stack<STATE>>();
		if (addInitial) {
			configurations.addAll(configurations);
		}
		for (Stack<STATE> config : configurations) {
			STATE state = config.pop();
			LETTER symbol = nw.getSymbol(position);
			if (nw.isInternalPosition(position)) {
				Iterable<STATE> succs = nwa.succInternal(state, symbol);
				for (STATE succ : succs) {
					Stack<STATE> succConfig = (Stack<STATE>) config.clone();
					succConfig.push(succ);
					succConfigs.add(succConfig);
				}
			} else if (nw.isCallPosition(position)) {
				Iterable<STATE> succs = nwa.succCall(state, symbol);
				for (STATE succ : succs) {
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
					Iterable<STATE> succs = nwa.succReturn(state, callPred, symbol);
					for (STATE succ : succs) {
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
