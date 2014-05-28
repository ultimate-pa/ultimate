package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.InCaReAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.ComplementDD;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.DifferenceBlackAndWhite;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.FinitePrefix2PetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetJulian;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetUnfolder;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetUnfolder.order;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopBenchmarkType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantAutomataBuilders.StraightLineInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;


public class CegarLoopJulian extends BasicCegarLoop {
	
	private BranchingProcess<CodeBlock, IPredicate> m_Unfolding;
	public int m_CoRelationQueries = 0;
	public int m_BiggestAbstractionTransitions;



	public CegarLoopJulian(String name, RootNode rootNode, SmtManager smtManager,
			TraceAbstractionBenchmarks timingStatistics,
			TAPreferences taPrefs, Collection<ProgramPoint> errorLocs) {
		super(name, rootNode, smtManager, taPrefs, errorLocs, INTERPOLATION.Craig_TreeInterpolation,
				false);

	}

	@Override
	protected void getInitialAbstraction() throws AutomataLibraryException {
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
			String filename = "Abstraction"+m_Iteration;
			writeAutomatonToFile(m_Abstraction, filename);
		}
	}
	

	
	@Override
	protected void constructInterpolantAutomaton() throws OperationCanceledException {
		m_CegarLoopBenchmark.start(CegarLoopBenchmarkType.s_BasicInterpolantAutomatonTime);
		StraightLineInterpolantAutomatonBuilder iab = 
				new StraightLineInterpolantAutomatonBuilder(
						new InCaReAlphabet<CodeBlock>(m_Abstraction),
						m_TraceChecker, m_PredicateFactoryInterpolantAutomata);
		m_InterpolAutomaton = iab.getResult();
			s_Logger.info("Interpolatants " + m_InterpolAutomaton.getStates());
			
			m_CegarLoopBenchmark.stop(CegarLoopBenchmarkType.s_BasicInterpolantAutomatonTime);	
		assert(accepts(m_InterpolAutomaton, m_Counterexample.getWord())) :
			"Interpolant automaton broken!";
		assert (m_SmtManager.checkInductivity(m_InterpolAutomaton, false, true));
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
			if (m_Pref.dumpAutomata()) {
				dumpNestedRun(m_Counterexample, m_IterationPW);
			}
			return false;
		}
	}
	
	
	
	
	
	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
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
				(new ComplementDD<CodeBlock, IPredicate>(m_PredicateFactoryInterpolantAutomata, dia)).getResult();
		assert(!accepts(nia, m_Counterexample.getWord())) : 
			"Complementation broken!";
		s_Logger.info("Complemented interpolant automaton has "+nia.getStates().size() +" states");

		if (m_Iteration <= m_Pref.watchIteration() && m_Pref.artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON) {
			m_ArtifactAutomaton = (NestedWordAutomaton<CodeBlock, IPredicate>) nia;
		}
		m_Abstraction = 
				(new DifferenceBlackAndWhite<CodeBlock, IPredicate>(
						abstraction, 
						(NestedWordAutomaton<CodeBlock, IPredicate>) dia)).getResult(); 

		m_CegarLoopBenchmark.reportAbstractionSize(m_Abstraction.size(), m_Iteration);
//		if (m_BiggestAbstractionSize < m_Abstraction.size()){
//			m_BiggestAbstractionSize = m_Abstraction.size();
//			m_BiggestAbstractionTransitions = abstraction.getTransitions().size();
//			m_BiggestAbstractionIteration = m_Iteration;
//		}


		assert(!acceptsPetriViaFA(m_Abstraction, m_Counterexample.getWord())) : "Intersection broken!";


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
			String filename = "Abstraction"+m_Iteration;
			writeAutomatonToFile(m_Abstraction, filename);
		}
		return true;
	}	
	
	


	@Override
	protected void computeCFGHoareAnnotation() {
		throw new UnsupportedOperationException();
	}
	
	private static boolean acceptsPetriViaFA(IAutomaton<CodeBlock, IPredicate> automaton, Word<CodeBlock> word) throws OperationCanceledException {
		NestedWord<CodeBlock> nw = NestedWord.nestedWord(word);
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> petriNetAsFA = (new PetriNet2FiniteAutomaton<CodeBlock, IPredicate>((IPetriNet<CodeBlock, IPredicate>) automaton)).getResult();
		return BasicCegarLoop.accepts(petriNetAsFA, nw);

	}
	

}
