package local.stalin.plugins.generator.traceabstractionconcurrent;

import local.stalin.automata.nwalibrary.NestedWordAutomaton;
import local.stalin.plugins.generator.rcfgbuilder.IProgramState;
import local.stalin.plugins.generator.rcfgbuilder.RootNode;
import local.stalin.plugins.generator.rcfgbuilder.TransAnnot;
import local.stalin.plugins.generator.traceabstraction.CegarLoopSequential;
import local.stalin.plugins.generator.traceabstraction.SmtManager;
import local.stalin.plugins.generator.traceabstraction.TAPreferences;
import local.stalin.plugins.generator.traceabstraction.TAPreferences.Artifact;


public class CegarLoopConcurrentAutomata extends CegarLoopSequential {

	public CegarLoopConcurrentAutomata(RootNode rootNode, SmtManager smtManager,
			TAPreferences taPrefs) {
		super(rootNode, smtManager, taPrefs);
//		m_ContentFactory = new TaConcurContentFactory(
//				rootNode.getRootAnnot().getLocNodes(),
//				this,
//				super.m_SmtManager.getTheory(),
//				super.m_HoareAnnotation,
//				false);
	}
	
	@Override
	protected void getInitialAbstraction() {
		CFG2Automaton cFG2NestedWordAutomaton =
			new Cfg2Nwa(m_RootNode,m_ContentFactory);
		m_Abstraction = (NestedWordAutomaton<TransAnnot, IProgramState>) cFG2NestedWordAutomaton.getResult();

		if (m_Iteration <= m_WatchIteration && 
				(m_Artifact == Artifact.ABSTRACTION || m_Artifact == Artifact.RCFG)) {
			m_ArtifactAutomaton = m_Abstraction;
		}
	}

}
