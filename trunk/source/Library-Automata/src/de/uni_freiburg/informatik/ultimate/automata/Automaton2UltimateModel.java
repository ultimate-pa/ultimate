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
package de.uni_freiburg.informatik.ultimate.automata;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.AlternatingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.visualization.AAToUltimateModel;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.visualization.NwaToUltimateModel;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.BranchingProcessToUltimateModel;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.PetriNetToUltimateModel;
import de.uni_freiburg.informatik.ultimate.model.IElement;


public class Automaton2UltimateModel<LETTER,STATE> {
	
	@SuppressWarnings({ "rawtypes", "unchecked" })
	public static IElement ultimateModel(IAutomaton automaton) throws OperationCanceledException {
		if (automaton instanceof INestedWordAutomatonSimple) {
			INestedWordAutomatonSimple nwa = (INestedWordAutomatonSimple) automaton;
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
		else if (automaton instanceof AlternatingAutomaton) {
			AlternatingAutomaton aa = (AlternatingAutomaton) automaton;
			AAToUltimateModel transformer = new AAToUltimateModel();
			return transformer.getUltimateModelOfAA(aa);
		}
		else {
			throw new IllegalArgumentException("Only nwa, aa and net supported");
		}
	}
}
