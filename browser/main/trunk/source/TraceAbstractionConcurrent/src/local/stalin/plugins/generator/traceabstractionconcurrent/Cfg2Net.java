package local.stalin.plugins.generator.traceabstractionconcurrent;

import local.stalin.automata.TestFileWriter;
import local.stalin.automata.nwalibrary.ContentFactory;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;
import local.stalin.automata.petrinet.jan.OperationsWithTests;
import local.stalin.automata.petrinet.jan.PetriNet;
import local.stalin.plugins.generator.rcfgbuilder.IProgramState;
import local.stalin.plugins.generator.rcfgbuilder.RootNode;
import local.stalin.plugins.generator.rcfgbuilder.TransAnnot;

public class Cfg2Net extends CFG2Automaton {

	private PetriNet<TransAnnot,IProgramState> m_Result;
	
	public Cfg2Net(RootNode rootNode,
			ContentFactory<IProgramState> contentFactory) {
		super(rootNode, contentFactory);
		
		constructProcedureAutomata();
		OperationsWithTests<TransAnnot, IProgramState> op = 
			new OperationsWithTests<TransAnnot,IProgramState>();
		m_Result = op.concurrentProduct(m_Automata.get(0));
//		new TestFileWriter<TransAnnot, IProgramState>(m_Automata.get(0), true);
		for (int i=1; i<m_Automata.size(); i++) {
			op.prefixProduct(m_Result, m_Automata.get(i));
//			new TestFileWriter<TransAnnot, IProgramState>(m_Automata.get(i), true);
		}
	}

	@Override
	public PetriNet<TransAnnot,IProgramState> getResult() {
		return m_Result;
	}

}
