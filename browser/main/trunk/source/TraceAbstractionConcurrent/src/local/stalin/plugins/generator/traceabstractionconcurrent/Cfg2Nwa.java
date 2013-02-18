package local.stalin.plugins.generator.traceabstractionconcurrent;

import local.stalin.automata.nwalibrary.ContentFactory;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;
import local.stalin.plugins.generator.rcfgbuilder.IProgramState;
import local.stalin.plugins.generator.rcfgbuilder.RootNode;
import local.stalin.plugins.generator.rcfgbuilder.TransAnnot;

public class Cfg2Nwa extends CFG2Automaton {
	
	private INestedWordAutomaton<TransAnnot,IProgramState> m_Result;

	public Cfg2Nwa(RootNode rootNode,
			ContentFactory<IProgramState> contentFactory) {
		super(rootNode, contentFactory);
		
		constructProcedureAutomata();
		m_Result = m_Automata.get(0);
		for (int i=1; i<m_Automata.size(); i++) {
			m_Result = ((NestedWordAutomaton<TransAnnot,IProgramState>)
					m_Result).getConcurrentPrefixProduct(m_Automata.get(i));
		}
		
	}
	
	@Override
	public INestedWordAutomaton<TransAnnot,IProgramState> getResult() {
		return m_Result;
	}
	

}
