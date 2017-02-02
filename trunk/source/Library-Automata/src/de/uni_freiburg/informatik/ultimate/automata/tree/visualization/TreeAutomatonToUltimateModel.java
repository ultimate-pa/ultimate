package de.uni_freiburg.informatik.ultimate.automata.tree.visualization;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.AutomatonState;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

public class TreeAutomatonToUltimateModel<LETTER, STATE> {
	public IElement transformToUltimateModel(final ITreeAutomatonBU<LETTER, STATE> ta) {
		System.out.println("implement in TreeAutomatonToUltimateModel");
		final AutomatonState graphroot = new AutomatonState("implement in TreeAutomatonToUltimateModel", false);
		return graphroot;
	}
}
