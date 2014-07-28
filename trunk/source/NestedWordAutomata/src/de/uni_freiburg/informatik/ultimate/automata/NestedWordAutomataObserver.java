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

import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.visualization.NwaToUltimateModel;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.BranchingProcessToUltimateModel;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.PetriNetToUltimateModel;
import de.uni_freiburg.informatik.ultimate.model.IElement;


public class NestedWordAutomataObserver implements IUnmanagedObserver {
	private static Logger s_Logger = 
			NestedWordAutomata.getLogger();
	
	private static IElement graphroot;


	/**
	 * 
	 * @return the root of the CFG.
	 */
	public IElement getRoot(){
		return NestedWordAutomataObserver.graphroot;
	}

	
	@SuppressWarnings("unchecked")
	@Override
	public boolean process(IElement node){
		Object printedAutomaton = parseAst(node);
		if (printedAutomaton == null) {
			NestedWordAutomaton<String,String> dummyAutomaton = 
				new NestedWordAutomaton<String,String>(
						new HashSet<String>(0), null, null, new StringFactory());
			dummyAutomaton.addState(true, false,
				"Use the Print keyword in .fat file to select an automaton" +
				" for visualization");
			printedAutomaton = dummyAutomaton;
		}
		
		try {
			if (printedAutomaton instanceof INestedWordAutomatonOldApi) {
				INestedWordAutomatonOldApi<String, String> nwa = 
						(INestedWordAutomatonOldApi<String, String>) printedAutomaton;
				NwaToUltimateModel<String, String> transformer = 
						new NwaToUltimateModel<String, String>();
				NestedWordAutomataObserver.graphroot = 
						transformer.getUltimateModelOfNwa(nwa);

			}

			else if (printedAutomaton instanceof IPetriNet) {
				IPetriNet<String, String> nwa = 
						(IPetriNet<String, String>) printedAutomaton;
				PetriNetToUltimateModel<String, String> transformer = 
						new PetriNetToUltimateModel<String, String>();
				NestedWordAutomataObserver.graphroot = 
						transformer.getUltimateModelOfPetriNet(nwa);
			}

			else if (printedAutomaton instanceof BranchingProcess) {
				BranchingProcess<String, String> net = 
						(BranchingProcess<String, String>) printedAutomaton;
				BranchingProcessToUltimateModel<String, String> transformer = 
						new BranchingProcessToUltimateModel<String, String>();
				NestedWordAutomataObserver.graphroot = 
						transformer.getUltimateModelOfBranchingProcess(net);
			}

			else {
				throw new UnsupportedOperationException("Only visualization of"
						+ " NWAs and PetriNet supported.");
			}
		} catch (OperationCanceledException e) {
			s_Logger.warn("Nothing visualized because of timeout");
		}
		return false;
	}
	

	/**
	 * Parses a Ultimate AST of an Automaton Test File. Performs all specified
	 * test cases. Logs information of every single test case. Logs if the
	 * result of all test cases was positive. 
	 * If some automaton is defined semantically incorrect, an unknown test case
	 * or operation is specified or the file contains several print test cases
	 * this method logs an error message.  
	 * @param Root node of a Ultimate AST of an Automaton Test File.
	 * @return the automaton that should be printed according to the Automaton
	 * Test File. Returns null if there is no print test case.
	 */
	private Object parseAst(IElement node) {
		return node;
	}

	@Override
	public void finish() {
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public void init() {
	}


	@Override
	public boolean performedChanges() {
		return false;
	}
	
	
	
	
	
	

	
	
	
	
	
}
