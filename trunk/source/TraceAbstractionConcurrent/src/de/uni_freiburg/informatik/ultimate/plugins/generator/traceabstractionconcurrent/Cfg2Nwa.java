package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class Cfg2Nwa extends CFG2Automaton {
	
	private INestedWordAutomatonOldApi<CodeBlock,IPredicate> m_Result;

	public Cfg2Nwa(RootNode rootNode,
			StateFactory<IPredicate> contentFactory, SmtManager smtManager) {
		super(rootNode, contentFactory, smtManager);
		
		constructProcedureAutomata();
		m_Result = m_Automata.get(0);
		for (int i=1; i<m_Automata.size(); i++) {
			m_Result = ((NestedWordAutomaton<CodeBlock,IPredicate>)
					m_Result).concurrentPrefixProduct(m_Automata.get(i));
		}
		
	}
	
	@Override
	public INestedWordAutomatonOldApi<CodeBlock,IPredicate> getResult() {
		return m_Result;
	}
	

}
