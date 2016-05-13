package de.uni_freiburg.informatik.ultimate.automata.tree.operators;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTA;

public class ConverterFTAToTree<LETTER extends RankedSymbol, STATE extends State> extends Converter {

	public TreeAutomatonBU<LETTER, STATE> convertToTree(GenFTA<LETTER, STATE> fta) {
		Set<LETTER> alphabet = new HashSet<LETTER>();
		for (LETTER letter : fta.getAlphabet()) {
			alphabet.add(letter);
		}
		
		TreeAutomatonBU<LETTER, STATE> result = new TreeAutomatonBU<LETTER, STATE>();
		for (FTARule<LETTER, STATE> rule : fta.getRules()) {
			List<STATE> srcState = new LinkedList<STATE>();
			for (STATE state : rule.getSrcStates()) {
				srcState.add(state);
			}
			result.addRule(rule.getSymbol(), srcState, rule.getDestState());
		}
		return result;
	}
}
