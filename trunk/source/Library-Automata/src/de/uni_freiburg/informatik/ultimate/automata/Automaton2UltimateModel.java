/*
 * Copyright (C) 2014-2015 Markus Pomrehn
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata;

import de.uni_freiburg.informatik.ultimate.automata.alternating.AlternatingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.alternating.visualization.AAToUltimateModel;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.NwaToUltimateModel;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.BranchingProcessToUltimateModel;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.PetriNetToUltimateModel;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.tree.visualization.TreeAutomatonToUltimateModel;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

/**
 * Converts an automaton (type {@link IAutomaton}) to an Ultimate model (type {@link IElement}).
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Markus Pomrehn
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public final class Automaton2UltimateModel {
	
	private Automaton2UltimateModel() {
		// private constructor
	}
	
	/**
	 * Converts an automaton ({@link IAutomaton}) object to an Ultimate model ({@link IElement}).
	 * 
	 * @param services
	 *            Ultimate services
	 * @param automaton
	 *            automaton
	 * @param <LETTER>
	 *            letter type
	 * @param <STATE>
	 *            state type
	 * @return Ultimate model of the automaton
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public static <LETTER, STATE> IElement ultimateModel(
			final AutomataLibraryServices services,
			final IAutomaton<LETTER, STATE> automaton)
					throws AutomataOperationCanceledException {
		if (automaton instanceof INestedWordAutomatonSimple) {
			final INestedWordAutomatonSimple<LETTER, STATE> nwa = (INestedWordAutomatonSimple<LETTER, STATE>) automaton;
			final NwaToUltimateModel<LETTER, STATE> transformer = new NwaToUltimateModel<>(services);
			return transformer.getUltimateModelOfNwa(nwa);
			
		} else if (automaton instanceof IPetriNet) {
			final IPetriNet<LETTER, STATE> net = (IPetriNet<LETTER, STATE>) automaton;
			final PetriNetToUltimateModel<LETTER, STATE> transformer = new PetriNetToUltimateModel<>();
			return transformer.getUltimateModelOfPetriNet(net);
			
		} else if (automaton instanceof BranchingProcess) {
			final BranchingProcess<LETTER, STATE> branchingProcess = (BranchingProcess<LETTER, STATE>) automaton;
			final BranchingProcessToUltimateModel<LETTER, STATE> transformer =
					new BranchingProcessToUltimateModel<>();
			return transformer.getUltimateModelOfBranchingProcess(branchingProcess);
			
		} else if (automaton instanceof AlternatingAutomaton) {
			final AlternatingAutomaton<LETTER, STATE> alternatingAutomaton =
					(AlternatingAutomaton<LETTER, STATE>) automaton;
			final AAToUltimateModel<LETTER, STATE> transformer = new AAToUltimateModel<>();
			return transformer.getUltimateModelOfAA(alternatingAutomaton);
			
		} else if (automaton instanceof ITreeAutomaton) {
			final ITreeAutomaton<LETTER, STATE> treeAutomaton = (ITreeAutomaton<LETTER, STATE>) automaton;
			final TreeAutomatonToUltimateModel<LETTER, STATE> transformer =
					new TreeAutomatonToUltimateModel<>();
			return transformer.getUltimateModelOfAA(treeAutomaton);
			
		} else {
			throw new IllegalArgumentException(
					"Only INestedWordAutomatonSimple, IPetriNet, BranchingProcess, "
							+ "AlternatingAutomaton, and ITreeAutomaton are supported");
		}
	}
}
