package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Complement;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.DifferenceBlackAndWhite;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.FinitePrefix2PetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetJulian;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetUnfolder;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetUnfolder.order;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.RunAnalyzer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TimingStatistics;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;


public class CegarLoopJulian extends BasicCegarLoop {
	
	private BranchingProcess<CodeBlock, IPredicate> m_Unfolding;
	public int m_CoRelationQueries = 0;
	public int m_BiggestAbstractionTransitions;



	public CegarLoopJulian(String name, RootNode rootNode, SmtManager smtManager,
			TimingStatistics timingStatistics,
			TAPreferences taPrefs, Collection<ProgramPoint> errorLocs) {
		super(name, rootNode, smtManager, timingStatistics, taPrefs, errorLocs);

	}

	@Override
	protected void getInitialAbstraction() throws OperationCanceledException {
		TaConcurContentFactory contentFactory = new TaConcurContentFactory(
				m_RootNode.getRootAnnot().getProgramPoints(),
				this,
				super.m_SmtManager,
				super.m_Pref,
				m_Pref.computeHoareAnnotation(),
				false);
		Cfg2NetJulian cFG2Automaton =
			new Cfg2NetJulian(m_RootNode, contentFactory, m_SmtManager);
		m_Abstraction = cFG2Automaton.getResult();

		if (m_Iteration <= m_Pref.watchIteration() && 
				(m_Pref.artifact() == Artifact.ABSTRACTION || m_Pref.artifact() == Artifact.RCFG)) {
			m_ArtifactAutomaton = m_Abstraction;
		}
		if (m_Pref.dumpAutomata()) {
			new AtsDefinitionPrinter<String,String>(m_Abstraction,
					m_Pref.dumpPath()+"/Abstraction"+m_Iteration,m_PrintAutomataLabeling,"");
		}
	}
	

	
	
	@Override
	protected boolean isAbstractionCorrect() throws OperationCanceledException {
		PetriNetJulian<CodeBlock, IPredicate> abstraction = 
				(PetriNetJulian<CodeBlock, IPredicate>) m_Abstraction;
		String orderString = m_Pref.order();
		boolean cutOffSameTrans = m_Pref.cutOffRequiresSameTransition();
		order ord;
		if (orderString.equals(order.KMM.getDescription())) {
			ord = order.KMM;
		} else if (orderString.equals(order.ERV.getDescription())) {
			ord = order.ERV;
		} else if (orderString.equals(order.ERV_MARK.getDescription())) {
			ord = order.ERV_MARK;
		} else {
			throw new IllegalArgumentException();
		}
		
		PetriNetUnfolder<CodeBlock,IPredicate> unf = 
				new PetriNetUnfolder<CodeBlock,IPredicate>(abstraction, ord, cutOffSameTrans, !m_Pref.unfoldingToNet());
		m_Unfolding = unf.getFinitePrefix();
		m_CoRelationQueries += m_Unfolding.getCoRelationQueries();

		m_Counterexample = unf.getAcceptingRun();
		if (m_Counterexample == null) {
			return true;
		}
		else {
			if (m_Pref.dumpFormulas() || m_Pref.dumpAutomata()) {
				dumpNestedRun(m_Counterexample, m_IterationPW);
			}
			m_RunAnalyzer = new RunAnalyzer(m_Counterexample);
			s_Logger.info("Found potential Counterexample");
			s_Logger.info("Cutpoints: " + m_RunAnalyzer.getCutpoints());
			s_Logger.debug(m_RunAnalyzer.getOccurence());
			return false;
		}
	}
	
	
	
	
	
	@Override
	protected boolean refineAbstraction() throws OperationCanceledException {
		PetriNetJulian<CodeBlock, IPredicate> abstraction =
				(PetriNetJulian<CodeBlock, IPredicate>) m_Abstraction;
		if (m_Pref.unfoldingToNet()) {
			abstraction = (new FinitePrefix2PetriNet<CodeBlock, IPredicate>(m_Unfolding)).getResult();	
		}
		
		//Determinize the interpolant automaton
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> dia = 
				determinizeInterpolantAutomaton();	

		//Complement the interpolant automaton
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> nia = 
				(new Complement<CodeBlock, IPredicate>(dia)).getResult();
		assert(!nia.accepts(m_Counterexample.getWord())) : 
			"Complementation broken!";
		s_Logger.info("Complemented interpolant automaton has "+nia.getStates().size() +" states");

		if (m_Iteration <= m_Pref.watchIteration() && m_Pref.artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON) {
			m_ArtifactAutomaton = (NestedWordAutomaton<CodeBlock, IPredicate>) nia;
		}
		m_Abstraction = 
				(new DifferenceBlackAndWhite<CodeBlock, IPredicate>(
						abstraction, 
						(NestedWordAutomaton<CodeBlock, IPredicate>) dia)).getResult(); 

		if (m_BiggestAbstractionSize < m_Abstraction.size()){
			m_BiggestAbstractionSize = m_Abstraction.size();
			m_BiggestAbstractionTransitions = abstraction.getTransitions().size();
			m_BiggestAbstractionIteration = m_Iteration;
		}


		assert(!m_Abstraction.accepts(m_Counterexample.getWord())) : "Intersection broken!";


		//		int[] statistic = m_Abstraction.transitions();
		//		s_Logger.debug("Abstraction has " +
		//				m_Abstraction.getAllStates().size() + "states, " + 
		//				statistic[0] + " internal transitions " + statistic[1] + 
		//				"call transitions " + statistic[2]+ " return transitions ");

		if (m_Iteration <= m_Pref.watchIteration() && 
				(m_Pref.artifact() == Artifact.ABSTRACTION || m_Pref.artifact() == Artifact.RCFG)) {
			m_ArtifactAutomaton = m_Abstraction;
		}
		if (m_Pref.dumpAutomata()) {
			String filename = m_Pref.dumpPath()+"/Abstraction"+m_Iteration;
			new AtsDefinitionPrinter<String,String>(m_Abstraction,filename,m_PrintAutomataLabeling, "");
		}
		return true;
	}	
	
	


	@Override
	protected void computeCFGHoareAnnotation() {
		throw new UnsupportedOperationException();
	}
	

}
