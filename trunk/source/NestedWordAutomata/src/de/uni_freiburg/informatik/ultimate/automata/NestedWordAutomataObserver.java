package de.uni_freiburg.informatik.ultimate.automata;

import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.visualization.NwaToUltimateModel;
import de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.StartNode;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.BranchingProcessToUltimateModel;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.PetriNetToUltimateModel;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.INode;


public class NestedWordAutomataObserver implements IUnmanagedObserver {
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
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
		Object printedAutomaton = parseAst( (INode) node);
		if (printedAutomaton == null) {
			NestedWordAutomaton<String,String> dummyAutomaton = 
				new NestedWordAutomaton<String,String>(
						new HashSet<String>(0), null, null, new StringFactory());
			dummyAutomaton.addState(true, false,
				"Use the Print keyword in .fat file to select an automaton" +
				" for visualization");
			printedAutomaton = dummyAutomaton;
		}
		
//		new TestFileWriter<String, String>(printedAutomaton);
		
		if (printedAutomaton instanceof INestedWordAutomaton) {
			INestedWordAutomaton<String,String> nwa =
				(INestedWordAutomaton<String,String>) printedAutomaton;
			
			NwaToUltimateModel<String, String> transformer = 
				new NwaToUltimateModel<String, String>();
			NestedWordAutomataObserver.graphroot = 
				transformer.getUltimateModelOfNwa(nwa);
		}
		
		else if (printedAutomaton instanceof IPetriNet) {
			IPetriNet<String,String> nwa =
				(IPetriNet<String,String>) printedAutomaton;
			PetriNetToUltimateModel<String, String> transformer = 
				new PetriNetToUltimateModel<String, String>();
			NestedWordAutomataObserver.graphroot = 
				transformer.getUltimateModelOfPetriNet(nwa);
		}
		
		else if (printedAutomaton instanceof BranchingProcess) {
			BranchingProcess<String,String> net =
				(BranchingProcess<String,String>) printedAutomaton;
			BranchingProcessToUltimateModel<String, String> transformer = 
				new BranchingProcessToUltimateModel<String, String>();
			NestedWordAutomataObserver.graphroot = 
				transformer.getUltimateModelOfBranchingProcess(net);
		}
		
		else {
			throw new UnsupportedOperationException("Only visualization of" +
					" NWAs and PetriNet supported.");
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
	private Object parseAst(INode node) {
		IAnnotations annot = 
			node.getPayload().getAnnotations().get("Automata Parser");
		assert (annot instanceof StartNode);
		TestFileExecutor tfe = new TestFileExecutor(node);
		return tfe.getPrintAutomaton();
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
