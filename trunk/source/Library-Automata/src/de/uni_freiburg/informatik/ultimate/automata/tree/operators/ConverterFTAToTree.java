package de.uni_freiburg.informatik.ultimate.automata.tree.operators;

import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTARule;

public class ConverterFTAToTree<LETTER, STATE extends State> extends Converter {

	public TreeAutomatonBU<LETTER, STATE> convertToTree(GenFTA<MySymbol<LETTER>, STATE> fta) {
		TreeAutomatonBU<LETTER, STATE> result = new TreeAutomatonBU<LETTER, STATE>();
		
		for (MySymbol<LETTER> letter : fta.getAlphabet()) {
			result.addLetter(letter.getLetter());
		}
		for (STATE state : fta.getStates()) {
			result.addState(state);
		}
		for (STATE state : fta.getFinalStates()) {
			result.addFinalState(state);
		}
		for (GenFTARule<MySymbol<LETTER>, STATE> rule : fta.getRules()) {
			List<STATE> srcState = new LinkedList<STATE>();
			for (STATE state : rule.getSrcStates()) {
				srcState.add(state);
			}
			result.addRule(rule.getSymbol().getLetter(), srcState, rule.getDestState());
			if (rule.getSymbol().getArity() == 0) {
				result.addInitialState(rule.getDestState());
			}
		}
		return result;
	}
}
