package local.stalin.plugins.generator.traceabstraction;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import local.stalin.SMTInterface.SMTInterface;
import local.stalin.automata.TestFileWriter;
import local.stalin.automata.TestFileWriter.Labeling;
import local.stalin.automata.nwalibrary.ContentFactory;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedRun;
import local.stalin.automata.nwalibrary.NestedWord;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;
import local.stalin.automata.nwalibrary.operations.DeterminizedAutomatonBuilder;
import local.stalin.automata.nwalibrary.operations.DifferenceAutomatonBuilder;
import local.stalin.automata.nwalibrary.operations.IStateDeterminizer;
import local.stalin.automata.nwalibrary.operations.PowersetSuccessorStateDeterminization;
import local.stalin.automata.nwalibrary.visualization.NwaToStalinModel;
import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.logic.Theory;
import local.stalin.model.INode;
import local.stalin.plugins.generator.rcfgbuilder.IProgramState;
import local.stalin.plugins.generator.rcfgbuilder.LocNode;
import local.stalin.plugins.generator.rcfgbuilder.ProgramPoint;
import local.stalin.plugins.generator.rcfgbuilder.RootNode;
import local.stalin.plugins.generator.rcfgbuilder.StateFormula;
import local.stalin.plugins.generator.rcfgbuilder.TransAnnot;
import local.stalin.plugins.generator.traceabstraction.CegarLoop.Result;
import local.stalin.plugins.generator.traceabstraction.TAPreferences.AdditionalEdges;
import local.stalin.plugins.generator.traceabstraction.TAPreferences.Artifact;
import local.stalin.plugins.generator.traceabstraction.TAPreferences.Determinization;
import local.stalin.plugins.generator.traceabstraction.TAPreferences.InterpolatedLocs;

public class CegarLoopSequential extends CegarLoop {

	final boolean interprocedural;
	protected ContentFactory<IProgramState> m_ContentFactory;

	
	protected NestedWordAutomaton<TransAnnot, IProgramState> m_Abstraction;
	protected NestedRun<TransAnnot, IProgramState> m_Counterexample;
	private RunAnalyzer m_RunAnalyzer;
	protected StateFormula[] m_Interpolants;
	protected NestedWordAutomaton<TransAnnot, IProgramState> interpolAutomaton;
	
	protected NestedWordAutomaton<TransAnnot, IProgramState> m_ArtifactAutomaton;
	
	
	// performance options

	protected final boolean m_SelfloopTrue;
	protected final InterpolatedLocs m_interpolatedLocs;
	protected final AdditionalEdges m_AdditionalEdges;
	protected final boolean m_DifferenceOperation;
	protected final Determinization m_Determinization;
	final boolean m_MinimizeAbstraction;
	
	protected final TAPreferences m_TaPrefs;
	
	protected final Labeling m_PrintAutomataLabeling = Labeling.TOSTRING;
	private RcfgHoareAnnotation rcfsHoareAnnotation;
	

	public CegarLoopSequential(RootNode rootNode,
			SmtManager smtManager,
			TAPreferences taPrefs) {
		
		super(rootNode, smtManager, taPrefs);
		interprocedural = taPrefs.interprocedural();
		this.m_TaPrefs = taPrefs;
		m_ContentFactory = new TAContentFactory(
				rootNode.getRootAnnot().getLocNodes(),
				this,
				super.m_SmtManager.getTheory(),
				m_TaPrefs,
				super.m_HoareAnnotation,
				interprocedural);
		m_SelfloopTrue = taPrefs.edges2True();
		s_Logger.warn("Interprodecural is " + interprocedural);
		
//		if (interpolatedLocs == InterpolatedLocs.CUTPOINTS) {
//			throw new UnsupportedOperationException("Cutpoint interpolation" +
//					" unsupported");
//		}
		m_interpolatedLocs = taPrefs.interpolatedLocs();
		if (taPrefs.additionalEdges() == AdditionalEdges.EAGER) {
			throw new UnsupportedOperationException("Eager" +
			" unsupported");
		}
		m_AdditionalEdges = taPrefs.additionalEdges();
		m_Determinization = taPrefs.determinization();
		m_DifferenceOperation = taPrefs.difference();
		m_MinimizeAbstraction = taPrefs.minimize();

		

	}
	
	
	
	


	@Override
	protected void getInitialAbstraction() {
		CFG2NestedWordAutomaton cFG2NestedWordAutomaton = 
			new CFG2NestedWordAutomaton(interprocedural);
		m_Abstraction = cFG2NestedWordAutomaton.getNestedWordAutomaton(
											super.m_RootNode, m_ContentFactory);
		if (m_Iteration <= m_WatchIteration && 
				(m_Artifact == Artifact.ABSTRACTION || m_Artifact == Artifact.RCFG)) {
			m_ArtifactAutomaton = m_Abstraction;
		}
		if (m_TaPrefs.dumpAutomata()) {
			new TestFileWriter<String,String>(m_Abstraction,
					m_DumpPath+"/Abstraction"+m_Iteration,m_PrintAutomataLabeling);
		}
		super.m_InitialAbstractionSize = m_Abstraction.getAllStates().size();
		super.m_BiggestAbstractionSize = m_Abstraction.getAllStates().size();
		super.m_NumberOfErrorLocations = m_Abstraction.getFinalStates().size();
	}
	
	@Override
	protected boolean isAbstractionCorrect() {			
		m_Counterexample = m_Abstraction.getAcceptingNestedRun();
		if (m_Counterexample == null) {
			return true;
		}
		else {
			if (m_DumpFormulas) {
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
	protected int isCounterexampleFeasible() {
		NestedInterpolantsBuilder nib = computeStateFormulasNested(m_Counterexample, 
				m_RunAnalyzer.getCutpoints()); 
		m_Interpolants = nib.getNestedInterpolants();

		if (m_Interpolants == null) {
			NestedWord<TransAnnot> counterexample = m_Counterexample.getNestedWord();
			for (int j=0; j<counterexample.length(); j++) {
				List<String> stmts = counterexample.getSymbolAt(j).getPrettyPrintedStatements();
				for (String st : stmts) {
					s_Logger.debug(st);
				}
			}
		}
		else {
			for (int j=0; j<m_Interpolants.length; j++) {
				s_Logger.debug("Interpolant "+j+": " + m_Interpolants[j]);
			}
		}
		return nib.isInputSatisfiable();
	}
	
	
	private NestedInterpolantsBuilder computeStateFormulasNested(
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
				interprocedural,
				interpolateAllLocations,
				set,
				m_Iteration, m_DumpFormulas, m_DumpPath, m_IterationPW);
		return nib;
	}
	
	
	
	
	@Override
	protected void constructInterpolantAutomaton() {
		Collection<TransAnnot> internalAlphabet = 
				m_Abstraction.getInternalAlphabet();
		Collection<TransAnnot> callAlphabet = 
				m_Abstraction.getCallAlphabet();
		Collection<TransAnnot> returnAlphabet = 
				m_Abstraction.getReturnAlphabet();


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

		assert (m_SmtManager.checkInductivity(interpolAutomaton));

		s_Logger.info("Interpolant Automaton has "+interpolAutomaton.getAllStates().size() +" states");
				
		if (m_Iteration <= m_WatchIteration && 
				m_Artifact == Artifact.INTERPOLANT_AUTOMATON) {
			m_ArtifactAutomaton = interpolAutomaton;
		}
		if (m_TaPrefs.dumpAutomata()) {
			new TestFileWriter<String,String>(interpolAutomaton,
					m_DumpPath+"/InterpolantAutomaton_Iteration"+m_Iteration,m_PrintAutomataLabeling);
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
			DifferenceAutomatonBuilder<TransAnnot, IProgramState> dab = 
				new DifferenceAutomatonBuilder<TransAnnot, IProgramState>(
													m_Abstraction,
													interpolAutomaton,
													stateDeterminizer,
													m_MinimizeAbstraction);
			m_Abstraction = (NestedWordAutomaton<TransAnnot, IProgramState>) dab.getResult();
			if (stateDeterminizer instanceof BestApproximationDeterminizer) {
				BestApproximationDeterminizer bed = 
					(BestApproximationDeterminizer)stateDeterminizer;
				s_Logger.info("Internal Transitions: " 
						+ bed.m_AnswerInternalAutomaton 
						+ " answers given by automaton " 
						+ bed.m_AnswerInternalCache 
						+ " answers given by cache " 
						+ bed.m_AnswerInternalSolver
						+ " answers given by solver");
				s_Logger.info("Call Transitions: " 
						+ bed.m_AnswerCallAutomaton 
						+ " answers given by automaton " 
						+ bed.m_AnswerCallCache 
						+ " answers given by cache " 
						+ bed.m_AnswerCallSolver
						+ " answers given by solver");
				s_Logger.info("Return Transitions: " 
						+ bed.m_AnswerReturnAutomaton 
						+ " answers given by automaton " 
						+ bed.m_AnswerReturnCache
						+ " answers given by cache " 
						+ bed.m_AnswerReturnSolver
						+ " answers given by solver");
			}
		}
		else {
			//Determinize the interpolant automaton
			DeterminizedAutomatonBuilder<TransAnnot, IProgramState> dab = 
				new DeterminizedAutomatonBuilder<TransAnnot, IProgramState>(interpolAutomaton, stateDeterminizer);
			
			INestedWordAutomaton<TransAnnot, IProgramState> dia = dab.getResult();
//			new TestFileWriter<TransAnnot, IProgramState>(dia, true);
			assert (m_SmtManager.checkInductivity(dia)) : 
				"Determinization broken - Not inductive";
			s_Logger.info("Nia is inductive");
			if (m_TaPrefs.dumpAutomata()) {
				new TestFileWriter<String,String>(dia,
						m_DumpPath+"/InterpolantAutomatonDeterminized_Iteration"+m_Iteration,m_PrintAutomataLabeling);
			}
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
			
			m_Abstraction = 
				(NestedWordAutomaton<TransAnnot, IProgramState>) m_Abstraction.intersect(nia);
		}
		
		if (m_BiggestAbstractionSize < m_Abstraction.getAllStates().size()){
			m_BiggestAbstractionSize = m_Abstraction.getAllStates().size();
			m_BiggestAbstractionIteration = m_Iteration;
		}

		assert(!m_Abstraction.accepts(m_Counterexample.getNestedWord())) : "Intersection broken!";
		assert (m_SmtManager.checkInductivity(m_Abstraction)) : 
			"abstraction not inductive";
		s_Logger.info("Abstraction is inductive");

		int[] statistic = m_Abstraction.transitions();
		s_Logger.debug("Abstraction has " +
				m_Abstraction.getAllStates().size() + "states, " + 
				statistic[0] + " internal transitions " + statistic[1] + 
				"call transitions " + statistic[2]+ " return transitions ");

		if (m_Iteration <= m_WatchIteration && 
				(m_Artifact == Artifact.ABSTRACTION || m_Artifact == Artifact.RCFG)) {
			m_ArtifactAutomaton = m_Abstraction;
		}
		
		if (m_TaPrefs.dumpAutomata()) {
			new TestFileWriter<String,String>(m_Abstraction,
					m_DumpPath+"/Abstraction"+m_Iteration,m_PrintAutomataLabeling);
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
					m_ArtifactAutomaton = (NestedWordAutomaton<TransAnnot, IProgramState>) m_ArtifactAutomaton.constructSingleEntryNwa(m_ArtifactAutomaton);
					NwaToStalinModel<TransAnnot,IProgramState> myTransformer = 
							new NwaToStalinModel<TransAnnot,IProgramState>();
					return myTransformer.getStalinModelOfNwa(m_ArtifactAutomaton);
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
		Map<String, Map<String, LocNode>> locNodes = m_RootNode.getRootAnnot().getLocNodes();
		Theory theory = m_RootNode.getRootAnnot().getTheory();
		for (IState<TransAnnot,IProgramState> state : m_Abstraction.getAllStates()) {
			IProgramState ps = state.getContent();
			String procName = ps.getProgramPoint().getProcedure();
			String locName = ps.getProgramPoint().getLocation();
			LocNode locNode = locNodes.get(procName).get(locName);
			locNode.getStateAnnot().addState(ps, theory);
		}

		if (m_TaPrefs.interprocedural())
		rcfsHoareAnnotation = new RcfgHoareAnnotation(m_Abstraction, m_RootNode.getRootAnnot(), m_SmtManager);
		boolean test = true;
	}
	

}