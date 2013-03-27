package de.uni_freiburg.informatik.ultimate.automata;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.visualization.NwaToUltimateModel;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.PetriNetToUltimateModel;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.INode;


public class Automaton2UltimateModel<LETTER,STATE> {
	
	@SuppressWarnings({ "rawtypes", "unchecked" })
	public static IElement ultimateModel(IAutomaton automaton) {
		if (automaton instanceof INestedWordAutomaton) {
			INestedWordAutomaton nwa = (INestedWordAutomaton) automaton;
			NwaToUltimateModel transformer = new NwaToUltimateModel();
				return transformer.getUltimateModelOfNwa(nwa);
		}
		else if (automaton instanceof IPetriNet) {
			IPetriNet net = (IPetriNet) automaton;
			PetriNetToUltimateModel transformer = new PetriNetToUltimateModel();
			return transformer.getUltimateModelOfPetriNet(net);
		}
		else {
			throw new IllegalArgumentException("Only nwa and net supported");
		}
	}
}
