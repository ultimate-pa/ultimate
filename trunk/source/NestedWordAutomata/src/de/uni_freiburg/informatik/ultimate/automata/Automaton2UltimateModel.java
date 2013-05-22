package de.uni_freiburg.informatik.ultimate.automata;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.visualization.NwaToUltimateModel;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.BranchingProcessToUltimateModel;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.PetriNetToUltimateModel;
import de.uni_freiburg.informatik.ultimate.model.IElement;


public class Automaton2UltimateModel<LETTER,STATE> {
	
	@SuppressWarnings({ "rawtypes", "unchecked" })
	public static IElement ultimateModel(IAutomaton automaton) throws OperationCanceledException {
		if (automaton instanceof INestedWordAutomatonOldApi) {
			INestedWordAutomatonOldApi nwa = (INestedWordAutomatonOldApi) automaton;
			NwaToUltimateModel transformer = new NwaToUltimateModel();
				return transformer.getUltimateModelOfNwa(nwa);
		}
		else if (automaton instanceof IPetriNet) {
			IPetriNet net = (IPetriNet) automaton;
			PetriNetToUltimateModel transformer = new PetriNetToUltimateModel();
			return transformer.getUltimateModelOfPetriNet(net);
		}
		else if (automaton instanceof BranchingProcess) {
			BranchingProcess bp = (BranchingProcess) automaton;
			BranchingProcessToUltimateModel transformer = new BranchingProcessToUltimateModel();
			return transformer.getUltimateModelOfBranchingProcess(bp);
		}
		else {
			throw new IllegalArgumentException("Only nwa and net supported");
		}
	}
}
