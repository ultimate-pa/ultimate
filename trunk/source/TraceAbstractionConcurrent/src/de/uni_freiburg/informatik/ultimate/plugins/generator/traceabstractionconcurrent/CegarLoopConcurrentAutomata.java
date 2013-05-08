package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TimingStatistics;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;




public class CegarLoopConcurrentAutomata extends BasicCegarLoop {

	public CegarLoopConcurrentAutomata(String name, RootNode rootNode, 
			SmtManager smtManager, TimingStatistics timingStatistics,
			TAPreferences taPrefs, Collection<ProgramPoint> errorLocs) {
		super(name, rootNode, smtManager, timingStatistics, taPrefs, errorLocs);
//		m_ContentFactory = new TaConcurContentFactory(
//				rootNode.getRootAnnot().getLocNodes(),
//				this,
//				super.m_SmtManager.getTheory(),
//				super.m_HoareAnnotation,
//				false);
	}
	
	@Override
	protected void getInitialAbstraction() {
		StateFactory<IPredicate> predicateFactory = new PredicateFactory(
				super.m_SmtManager,
				m_Pref);
		CFG2Automaton cFG2NestedWordAutomaton =
			new Cfg2Nwa(m_RootNode,predicateFactory,m_SmtManager);
		m_Abstraction = (NestedWordAutomaton<CodeBlock, IPredicate>) cFG2NestedWordAutomaton.getResult();

		if (m_Iteration <= m_Pref.watchIteration() && 
				(m_Pref.artifact() == Artifact.ABSTRACTION || m_Pref.artifact() == Artifact.RCFG)) {
			m_ArtifactAutomaton = m_Abstraction;
		}
	}

}
