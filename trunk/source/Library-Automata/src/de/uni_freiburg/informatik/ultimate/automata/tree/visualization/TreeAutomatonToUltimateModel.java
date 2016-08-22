package de.uni_freiburg.informatik.ultimate.automata.tree.visualization;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.AutomatonState;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

public class TreeAutomatonToUltimateModel<LETTER, STATE> {
	public IElement getUltimateModelOfAA(ITreeAutomaton<LETTER,STATE> ta) throws AutomataOperationCanceledException {
		System.out.println("implement in TreeAutomatonToUltimateModel");
		final AutomatonState graphroot = new AutomatonState("implement in TreeAutomatonToUltimateModel",false);	
		return graphroot;
	}
	
}
