package de.uni_freiburg.informatik.ultimate.automata.tree.operators;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTACreator;

/**
 * Ultimate's TreeAutomaton to Lethal GenFTA converter.
 * 
 * 
 * @param <LETTER> is the type of the alphabet.
 * @param <STATE> is the type of the states.
 * 
 * @author Mostafa M.A.
 */
public class ConverterToFTA<LETTER, STATE> extends Converter {
	
	public GenFTA<MySymbol<LETTER>, MyState<STATE>> convertITreeToFTA(TreeAutomatonBU<LETTER, STATE> tree) {
		GenFTACreator<MySymbol<LETTER>, MyState<STATE>> g = new GenFTACreator<MySymbol<LETTER>, MyState<STATE>>();
		Map<STATE, MyState<STATE>> myStates = new HashMap<STATE, MyState<STATE>>();
		Map<LETTER, MySymbol<LETTER>> mySymbols = new HashMap<LETTER, MySymbol<LETTER>>();
		Collection<FTARule<MySymbol<LETTER>, MyState<STATE>>> rules = new LinkedList<FTARule<MySymbol<LETTER>, MyState<STATE>>>();
		
		LinkedList<STATE> queue = new LinkedList<STATE>();
		
		for (STATE state : tree.getStates()) {
			queue.add(state);
			myStates.put(state, new MyState<STATE>(state));
		}
		
		while (!queue.isEmpty()) {
			STATE state = queue.poll();
			MyState<STATE> myState = myStates.get(state);
			
			Map<LETTER, Iterable<List<STATE>>> predecessors = tree.getPredecessors(state);
			for (LETTER letter : predecessors.keySet()) {
				if (!mySymbols.containsKey(letter)) {
					mySymbols.put(letter, new MySymbol<LETTER>(letter, predecessors.get(letter).iterator().next().size()));
				}
				MySymbol<LETTER> mySymbol = mySymbols.get(letter);
				for (List<STATE> stateCombination : predecessors.get(letter)) {
					List<MyState<STATE>> pred = new LinkedList<MyState<STATE>>();
					for (STATE nextState : stateCombination) {
						if (!myStates.containsKey(nextState)) {
							myStates.put(nextState, new MyState<STATE>(nextState));
							queue.add(nextState);
						}
						pred.add(myStates.get(nextState));
					}
					rules.add(g.createRule(mySymbol, pred, myState));
				}
			}
		}
		Collection<MyState<STATE>> finalStates = new HashSet<MyState<STATE>>();
		for (STATE state : myStates.keySet()) {
			if (tree.isFinalState(state)) {
				finalStates.add(myStates.get(state));
			}
		}
		return g.createFTA(mySymbols.values(), myStates.values(), finalStates, rules);
	}
}
