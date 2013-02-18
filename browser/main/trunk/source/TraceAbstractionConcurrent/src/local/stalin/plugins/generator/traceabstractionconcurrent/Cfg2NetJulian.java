package local.stalin.plugins.generator.traceabstractionconcurrent;

import local.stalin.automata.nwalibrary.ContentFactory;
import local.stalin.automata.petrinet.julian.PetriNetJulian;
import local.stalin.plugins.generator.rcfgbuilder.IProgramState;
import local.stalin.plugins.generator.rcfgbuilder.RootNode;
import local.stalin.plugins.generator.rcfgbuilder.TransAnnot;

public class Cfg2NetJulian extends CFG2Automaton {

	private PetriNetJulian<TransAnnot, IProgramState> m_Result;
	
	public Cfg2NetJulian(RootNode rootNode,
			ContentFactory<IProgramState> contentFactory) {
		super(rootNode, contentFactory);
		
		constructProcedureAutomata();
		m_Result = new PetriNetJulian<TransAnnot,IProgramState>(m_Automata.get(0));
//		new TestFileWriter<TransAnnot, IProgramState>(m_Automata.get(0), true);
		for (int i=1; i<m_Automata.size(); i++) {
			m_Result = (PetriNetJulian<TransAnnot, IProgramState>) m_Result.prefixProduct(m_Result, m_Automata.get(i));
//			new TestFileWriter<TransAnnot, IProgramState>(m_Automata.get(i), true);
		}
	}

	@Override
	public PetriNetJulian<TransAnnot,IProgramState> getResult() {
		return m_Result;
	}

}
