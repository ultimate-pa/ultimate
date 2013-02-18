package local.stalin.automata;

import local.stalin.access.IUnmanagedObserver;
import local.stalin.access.WalkerOptions;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;
import local.stalin.automata.nwalibrary.visualization.NwaToStalinModel;
import local.stalin.automata.parser.astAnnotations.StartNode;
import local.stalin.automata.petrinet.IPetriNet;
import local.stalin.automata.petrinet.jan.IOccurrenceNet;
import local.stalin.automata.petrinet.visualization.OccurenceNetToStalinModel;
import local.stalin.automata.petrinet.visualization.PetriNetToStalinModel;
import local.stalin.core.api.StalinServices;
import local.stalin.model.IAnnotations;
import local.stalin.model.IElement;
import local.stalin.model.INode;

import org.apache.log4j.Logger;


public class NestedWordAutomataObserver implements IUnmanagedObserver {
	private static Logger s_Logger = 
			StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private static INode graphroot;


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
				new NestedWordAutomaton<String,String>(null, null, null, null);
			dummyAutomaton.addState(true, false,
				"Use the Print keyword in .fat file to select an automaton" +
				" for visualization");
			printedAutomaton = dummyAutomaton;
		}
		
		new TestFileWriter<String, String>(printedAutomaton);
		
		if (printedAutomaton instanceof NestedWordAutomaton) {
			NestedWordAutomaton<String,String> nwa =
				(NestedWordAutomaton<String,String>) printedAutomaton;
			
			NwaToStalinModel<String, String> transformer = 
				new NwaToStalinModel<String, String>();
			NestedWordAutomataObserver.graphroot = 
				transformer.getStalinModelOfNwa(nwa);
		}
		
		else if (printedAutomaton instanceof IPetriNet) {
			IPetriNet<String,String> nwa =
				(IPetriNet<String,String>) printedAutomaton;
			PetriNetToStalinModel<String, String> transformer = 
				new PetriNetToStalinModel<String, String>();
			NestedWordAutomataObserver.graphroot = 
				transformer.getStalinModelOfPetriNet(nwa);
		}
		
		else if (printedAutomaton instanceof IOccurrenceNet) {
			IOccurrenceNet<String,String> net =
				(IOccurrenceNet<String,String>) printedAutomaton;
			OccurenceNetToStalinModel<String, String> transformer = 
				new OccurenceNetToStalinModel<String, String>();
			NestedWordAutomataObserver.graphroot = 
				transformer.getStalinModelOfOcurrenceNet(net);
		}
		
		else {
			throw new UnsupportedOperationException("Only visualization of" +
					" NWAs and PetriNet supported.");
		}
		return false;
	}
	

	/**
	 * Parses a STALIN AST of an Automaton Test File. Performs all specified
	 * test cases. Logs information of every single test case. Logs if the
	 * result of all test cases was positive. 
	 * If some automaton is defined semantically incorrect, an unknown test case
	 * or operation is specified or the file contains several print test cases
	 * this method logs an error message.  
	 * @param Root node of a STALIN AST of an Automaton Test File.
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
