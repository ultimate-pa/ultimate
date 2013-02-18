package local.stalin.plugins.generator.traceabstractionconcurrent;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

import local.stalin.SMTInterface.SMTInterface;
import local.stalin.automata.TestFileWriter;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.NestedRun;
import local.stalin.automata.nwalibrary.NestedWord;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;
import local.stalin.automata.nwalibrary.operations.DeterminizedAutomatonBuilder;
import local.stalin.automata.nwalibrary.operations.IStateDeterminizer;
import local.stalin.automata.nwalibrary.operations.PowersetSuccessorStateDeterminization;
import local.stalin.automata.petrinet.jan.OperationsWithTests;
import local.stalin.automata.petrinet.jan.PetriNet;
import local.stalin.automata.petrinet.visualization.PetriNetToStalinModel;
import local.stalin.model.INode;
import local.stalin.plugins.generator.rcfgbuilder.IProgramState;
import local.stalin.plugins.generator.rcfgbuilder.ProgramPoint;
import local.stalin.plugins.generator.rcfgbuilder.RootNode;
import local.stalin.plugins.generator.rcfgbuilder.StateFormula;
import local.stalin.plugins.generator.rcfgbuilder.TransAnnot;
import local.stalin.plugins.generator.traceabstraction.BestApproximationDeterminizer;
import local.stalin.plugins.generator.traceabstraction.CegarLoopSequential;
import local.stalin.plugins.generator.traceabstraction.InterpolantAutomataBuilder;
import local.stalin.plugins.generator.traceabstraction.NestedInterpolantsBuilder;
import local.stalin.plugins.generator.traceabstraction.NestedSsaBuilder;
import local.stalin.plugins.generator.traceabstraction.SmtManager;
import local.stalin.plugins.generator.traceabstraction.TAPreferences;
import local.stalin.plugins.generator.traceabstraction.TAPreferences.Artifact;

public class CegarLoopConcurrent extends CegarLoopSequential {
	
	PetriNet<TransAnnot, IProgramState> m_Abstraction;
	Object m_ArtifactAutomaton;

	public CegarLoopConcurrent(RootNode rootNode, SmtManager smtManager,
			TAPreferences taPrefs) {
		super(rootNode, smtManager, taPrefs);
	}

	@Override
	protected void getInitialAbstraction() {
		m_ContentFactory = new TaConcurContentFactory(
				m_RootNode.getRootAnnot().getLocNodes(),
				this,
				super.m_SmtManager.getTheory(),
				super.m_TaPrefs,
				super.m_HoareAnnotation,
				false);
		Cfg2Net cFG2Automaton =
			new Cfg2Net(m_RootNode,m_ContentFactory);
		m_Abstraction = cFG2Automaton.getResult();

		if (m_Iteration <= m_WatchIteration && 
				(m_Artifact == Artifact.ABSTRACTION || m_Artifact == Artifact.RCFG)) {
			m_ArtifactAutomaton = m_Abstraction;
		}
	}
	
	
	@Override
	protected boolean isAbstractionCorrect() {
//		new TestFileWriter<String,String>(m_Abstraction,"TheNet",1);
		m_Counterexample = m_Abstraction.getAcceptedWord();
		if (m_Counterexample == null) {
			return true;
		}
		else {
			if (m_DumpFormulas) {
//				dumpNestedRun(m_Counterexample, m_IterationPW);
			}
//			m_RunAnalyzer = new RunAnalyzer(m_Counterexample);
//			s_Logger.info("Found potential Counterexample");
//			s_Logger.info("Cutpoints: " + m_RunAnalyzer.getCutpoints());
//			s_Logger.debug(m_RunAnalyzer.getOccurence());
			return false;
		}
	}
	
	

	@Override
	protected int isCounterexampleFeasible() {
		m_Interpolants = computeStateFormulasNested(m_Counterexample, 
												null);

		if (m_Interpolants == null) {
			NestedWord<TransAnnot> counterexample = m_Counterexample.getNestedWord();
			for (int j=0; j<counterexample.length(); j++) {
				List<String> stmts = counterexample.getSymbolAt(j).getPrettyPrintedStatements();
				for (String st : stmts) {
					s_Logger.debug(st);
				}
			}
			return SMTInterface.SMT_UNKNOWN;
		}
		else {
			for (int j=0; j<m_Interpolants.length; j++) {
				s_Logger.debug("Interpolant "+j+": " + m_Interpolants[j]);
			}
			return SMTInterface.SMT_UNSAT;
		}
	}
	
	private StateFormula[] computeStateFormulasNested(
			NestedRun<TransAnnot, IProgramState> run,
			 Set<ProgramPoint> set
			) {
		
		NestedSsaBuilder nsb = new NestedSsaBuilder(m_SmtManager, run.getNestedWord(), m_IterationPW, m_DumpFormulas);
		nsb.buildSSA();
		
		boolean interpolateAllLocations;
		switch (m_interpolatedLocs) {
		case ALL:
			interpolateAllLocations = true;
			break;
		case CUTPOINTS:
			interpolateAllLocations = false;
			break;
		default:
			throw new IllegalArgumentException();
		}
		
		NestedInterpolantsBuilder nib = new NestedInterpolantsBuilder(
				m_SmtManager,
				run, 
				nsb.getSSA(), 
				nsb.getLocalVarAssignment(),
				nsb.getGlobalOldVarAssignment(),
				nsb.getConstants2VarNames(),
				nsb.getConstants2OldVarNames(),
				false,
				interpolateAllLocations,
				set,
				m_Iteration, m_DumpFormulas, m_DumpPath, m_IterationPW);
		return nib.getNestedInterpolants();
	}
	
	
	
	
	
	
	
	
	@Override
	protected void constructInterpolantAutomaton() {
		Collection<TransAnnot> internalAlphabet = 
				m_Abstraction.getAlphabet();
		Collection<TransAnnot> callAlphabet = new ArrayList<TransAnnot>(0);
		Collection<TransAnnot> returnAlphabet = new ArrayList<TransAnnot>(0);



		InterpolantAutomataBuilder iab = 
			new InterpolantAutomataBuilder(
					m_Counterexample,
					m_AdditionalEdges,
					m_SmtManager,
					m_Iteration,
					m_DumpFormulas,	m_DumpPath, m_IterationPW, m_SelfloopTrue);
		interpolAutomaton = iab.buildInterpolantAutomaton(
				m_Interpolants, 
				internalAlphabet, callAlphabet, returnAlphabet, 
				m_ContentFactory);
		assert(interpolAutomaton.accepts(m_Counterexample.getNestedWord())) :
			"Interpolant automaton broken!";

		m_SmtManager.checkInductivity(interpolAutomaton);

		s_Logger.info("Interpolant Automaton has "+interpolAutomaton.getAllStates().size() +" states");
				
		if (m_Iteration <= m_WatchIteration && 
				m_Artifact == Artifact.INTERPOLANT_AUTOMATON) {
			m_ArtifactAutomaton = interpolAutomaton;
		}

	}
	
	
	
	@Override
	protected void refineAbstraction() {
		
		IStateDeterminizer<TransAnnot,IProgramState> stateDeterminizer;
		switch (m_Determinization) {
		case POWERSET:
			stateDeterminizer =	new PowersetSuccessorStateDeterminization<TransAnnot,
											IProgramState>(m_ContentFactory);
			break;
		case BESTAPPROXIMATION:
			stateDeterminizer = new BestApproximationDeterminizer(m_SmtManager,
						  					m_ContentFactory,
						  					interpolAutomaton);
			break;
		default:
			throw new UnsupportedOperationException();
		}
		
		if (m_DifferenceOperation) {
			throw new UnsupportedOperationException();
		}
		else {
			//Determinize the interpolant automaton
			DeterminizedAutomatonBuilder<TransAnnot, IProgramState> dab = 
				new DeterminizedAutomatonBuilder<TransAnnot, IProgramState>(interpolAutomaton, stateDeterminizer);
			
			INestedWordAutomaton<TransAnnot, IProgramState> dia = dab.getResult();
//			new TestFileWriter<TransAnnot, IProgramState>(dia, true);
			assert (m_SmtManager.checkInductivity(dia)) : 
				"Determinization broken - Not inductive";
			assert(dia.accepts(m_Counterexample.getNestedWord())) : 
				"Determinization broken - No progress!";

			//Complement the interpolant automaton
			NestedWordAutomaton<TransAnnot, IProgramState> nia = 
				(NestedWordAutomaton<TransAnnot, IProgramState>) dia.complement();
			assert(!nia.accepts(m_Counterexample.getNestedWord())) : 
				"Complementation broken!";
			s_Logger.info("Complemented interpolant automaton has "+nia.getAllStates().size() +" states");
			
			if (m_Iteration <= m_WatchIteration && m_Artifact == Artifact.NEG_INTERPOLANT_AUTOMATON) {
				m_ArtifactAutomaton = (NestedWordAutomaton<TransAnnot, IProgramState>) nia;
			}
			m_Abstraction = (PetriNet<TransAnnot, IProgramState>) 
				(new OperationsWithTests<TransAnnot, IProgramState>()).
				selfloopIntersection(m_Abstraction, nia);
//			new OperationsWithTests<TransAnnot, IProgramState>().concurrentProduct(m_Abstraction, nia);
		}
		

		assert(!m_Abstraction.accepts(m_Counterexample.getNestedWord())) : "Intersection broken!";


//		int[] statistic = m_Abstraction.transitions();
//		s_Logger.debug("Abstraction has " +
//				m_Abstraction.getAllStates().size() + "states, " + 
//				statistic[0] + " internal transitions " + statistic[1] + 
//				"call transitions " + statistic[2]+ " return transitions ");

		if (m_Iteration <= m_WatchIteration && 
				(m_Artifact == Artifact.ABSTRACTION || m_Artifact == Artifact.RCFG)) {
			m_ArtifactAutomaton = m_Abstraction;
		}
	}	
	
	
	@Override
	public INode getArtifact() {
		if (m_Artifact == Artifact.ABSTRACTION ||
				m_Artifact == Artifact.INTERPOLANT_AUTOMATON ||
				m_Artifact == Artifact.NEG_INTERPOLANT_AUTOMATON) {

				if (m_ArtifactAutomaton == null) {
					s_Logger.info("Preferred Artifact not available," +
							" visualizing the RCFG instead");
					return m_RootNode;
				}
				else {
					PetriNetToStalinModel<TransAnnot,IProgramState> myTransformer = 
							new PetriNetToStalinModel<TransAnnot,IProgramState>();
					return myTransformer.getStalinModelOfPetriNet((PetriNet<TransAnnot, IProgramState>) m_ArtifactAutomaton);
				}
			}
			else if (m_Artifact == Artifact.RCFG) {
				computeCFGHoareAnnotation();
				return m_RootNode;
			}
			else {
				throw new IllegalArgumentException();
			}
	}



	@Override
	protected void computeCFGHoareAnnotation() {
		throw new UnsupportedOperationException();
	}
	

}
