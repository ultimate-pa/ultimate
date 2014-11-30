package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetJulian;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PrefixProduct;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class Cfg2NetJulian extends CFG2Automaton {

	private PetriNetJulian<CodeBlock, IPredicate> m_Result;
	
	public Cfg2NetJulian(RootNode rootNode,
			StateFactory<IPredicate> contentFactory, SmtManager smtManager, IUltimateServiceProvider services)
					throws AutomataLibraryException {
		super(rootNode, contentFactory, smtManager, services);
		
		constructProcedureAutomata();
		m_Result = new PetriNetJulian<CodeBlock,IPredicate>(services,m_Automata.get(0));
//		new TestFileWriter<TransAnnot, Predicate>(m_Automata.get(0), true);
		for (int i=1; i<m_Automata.size(); i++) {
			m_Result = (new PrefixProduct<CodeBlock,IPredicate>(
					services, m_Result, m_Automata.get(i)).getResult());
//			new TestFileWriter<TransAnnot, Predicate>(m_Automata.get(i), true);
		}
	}

	@Override
	public PetriNetJulian<CodeBlock,IPredicate> getResult() {
		return m_Result;
	}

}
