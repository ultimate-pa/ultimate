package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.Automaton2UltimateModel;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.ComplementDD;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DeterminizeDD;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DifferenceDD;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IntersectDD;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.BestApproximationDeterminizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.PostDeterminizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.SelfloopDeterminizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.StrongestPostDeterminizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker.AllIntegers;

/**
 * Subclass of AbstractCegarLoop which provides all algorithms for checking
 * safety (not termination).
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BasicCegarLoop extends AbstractCegarLoop {
	
	private final static boolean differenceInsteadOfIntersection = true;
	
	private final static boolean m_RemoveDeadEnds = true;

	
	protected HoareAnnotationFragments m_Haf;

	protected RunAnalyzer m_RunAnalyzer;

	private IPredicate m_TruePredicate;

	private IPredicate m_FalsePredicate;

	private IPredicate[] m_Interpolants;

	private PredicateFactoryRefinement m_StateFactoryForRefinement;
	
	private final TimingStatistics m_TimingStatistics;


	
	
	public BasicCegarLoop(String name, RootNode rootNode,
			SmtManager smtManager,
			TimingStatistics timingStatistics,
			TAPreferences taPrefs,
			Collection<ProgramPoint> errorLocs) {
	
		super(name, rootNode, smtManager, taPrefs, errorLocs);
		m_TimingStatistics = timingStatistics;
		m_Haf = new HoareAnnotationFragments(rootNode.getRootAnnot(),super.m_SmtManager);
		m_StateFactoryForRefinement = new PredicateFactoryRefinement(
				m_RootNode.getRootAnnot().getProgramPoints(),
				this,
				super.m_SmtManager,
				m_Pref,
				m_RemoveDeadEnds && m_Pref.computeHoareAnnotation(),
				m_Haf);
	}
	
	
	
	


	@Override
	protected void getInitialAbstraction() throws OperationCanceledException {
		CFG2NestedWordAutomaton cFG2NestedWordAutomaton = 
			new CFG2NestedWordAutomaton(m_Pref, super.m_SmtManager);
		PredicateFactory defaultStateFactory = new PredicateFactory(
				super.m_SmtManager,
				m_Pref);
		
		m_Abstraction = cFG2NestedWordAutomaton.getNestedWordAutomaton(
						super.m_RootNode, defaultStateFactory, super.m_ErrorLocs);
	}
	
	
	
	
	
	@Override
	protected boolean isAbstractionCorrect() throws OperationCanceledException {			
		try {
			m_Counterexample = m_Abstraction.acceptingRun();
		} catch (OperationCanceledException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
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
	protected LBool isCounterexampleFeasible() {
		m_TimingStatistics.startTraceCheck();
		m_TraceChecker = new TraceChecker(m_SmtManager,
				m_RootNode.getRootAnnot().getModifiedVars(),
				m_RootNode.getRootAnnot().getEntryNodes(),
				m_IterationPW);
		m_TruePredicate = m_SmtManager.newTruePredicate();
		m_FalsePredicate = m_SmtManager.newFalsePredicate();
		
		LBool feasibility = m_TraceChecker.checkTrace(
				m_TruePredicate, m_FalsePredicate, m_Counterexample.getWord());
		if (feasibility != LBool.UNSAT) {
			s_Logger.info("Counterexample might be feasible");
			NestedWord<CodeBlock> counterexample = NestedWord.nestedWord(m_Counterexample.getWord());
			String indentation = "";
			indentation += "  ";
			for (int j=0; j < counterexample.length(); j++) {
				String stmts = counterexample.getSymbol(j).getPrettyPrintedStatements();
				System.out.println(indentation + stmts);
//				s_Logger.info(indentation + stmts);
				if (counterexample.isCallPosition(j)) {
					indentation += "    "; 
				}
				if (counterexample.isReturnPosition(j)) {
					indentation = indentation.substring(0, indentation.length()-4); 
				}
			}
			m_FailurePath = m_TraceChecker.getFailurePath();
		} else {
			AllIntegers allInt = new TraceChecker.AllIntegers();
			m_Interpolants = m_TraceChecker.getInterpolants(allInt);
		}
		m_TimingStatistics.finishTraceCheck();
		return feasibility;
	}
	
	

	
	
	@Override
	protected void constructInterpolantAutomaton() {
		m_TimingStatistics.startBasicInterpolantAutomaton();
		InterpolantAutomataBuilder iab = new InterpolantAutomataBuilder(
						m_Counterexample,
						m_TruePredicate,
						m_FalsePredicate,
						m_Interpolants,
						m_Pref.interpolantAutomaton(), m_Pref.edges2True(),
						m_SmtManager, m_Pref,
						m_Iteration, m_IterationPW);
		m_InterpolAutomaton = iab.buildInterpolantAutomaton(
				m_Abstraction, m_Abstraction.getStateFactory());
		m_TimingStatistics.finishBasicInterpolantAutomaton();		
		assert(m_InterpolAutomaton.accepts(m_Counterexample.getWord())) :
			"Interpolant automaton broken!";
		assert (m_SmtManager.checkInductivity(m_InterpolAutomaton, false, true));
	}
	
	

	
	
	
	@Override
	protected boolean refineAbstraction() throws OperationCanceledException {
//		howDifferentAreInterpolants(m_InterpolAutomaton.getStates());
		
		m_TimingStatistics.startDifference();
		boolean explointSigmaStarConcatOfIA = !m_Pref.computeHoareAnnotation();
		
		PredicateFactory predicateFactory = (PredicateFactory) m_Abstraction.getStateFactory();
		
		NestedWordAutomaton<CodeBlock, IPredicate> oldAbstraction = 
				(NestedWordAutomaton<CodeBlock, IPredicate>) m_Abstraction;
		Map<IPredicate, Set<IPredicate>> removedDoubleDeckers = null;
		Map<IPredicate, IPredicate> context2entry = null;
		if (differenceInsteadOfIntersection) {
			s_Logger.debug("Start constructing difference");
			assert(oldAbstraction.getStateFactory() == m_InterpolAutomaton.getStateFactory());
			
			IOpWithDelayedDeadEndRemoval<CodeBlock, IPredicate> diff;
			
			switch (m_Pref.determinization()) {
			case POWERSET:
				PowersetDeterminizer<CodeBlock, IPredicate> psd = 
					new PowersetDeterminizer<CodeBlock, IPredicate>(m_InterpolAutomaton);
				if (m_Pref.differenceSenwa()) {
					diff = new DifferenceSenwa<CodeBlock, IPredicate>(
								oldAbstraction, m_InterpolAutomaton, psd, false);
				} else {
					diff = new DifferenceDD<CodeBlock, IPredicate>(
							oldAbstraction, m_InterpolAutomaton, psd, 
							m_StateFactoryForRefinement,
							false,
							explointSigmaStarConcatOfIA);
				}
			break;
			case BESTAPPROXIMATION:	
				BestApproximationDeterminizer bed = 
					new BestApproximationDeterminizer(m_SmtManager,	m_Pref, 
											m_InterpolAutomaton);
				diff = new DifferenceDD<CodeBlock, IPredicate>(
							oldAbstraction, m_InterpolAutomaton, bed,
							m_StateFactoryForRefinement,
							false, explointSigmaStarConcatOfIA);
				
				s_Logger.info("Internal Transitions: " 
						+ bed.m_AnswerInternalAutomaton + " answers given by automaton "
						+ bed.m_AnswerInternalCache	+ " answers given by cache "
						+ bed.m_AnswerInternalSolver + " answers given by solver");
				s_Logger.info("Call Transitions: " 
						+ bed.m_AnswerCallAutomaton	+ " answers given by automaton "
						+ bed.m_AnswerCallCache + " answers given by cache "
						+ bed.m_AnswerCallSolver + " answers given by solver");
				s_Logger.info("Return Transitions: "
						+ bed.m_AnswerReturnAutomaton + " answers given by automaton "
						+ bed.m_AnswerReturnCache + " answers given by cache "
						+ bed.m_AnswerReturnSolver + " answers given by solver");
			break;
			
			case EAGERPOST:	
				PostDeterminizer epd = new PostDeterminizer(m_SmtManager, m_Pref, 
									m_InterpolAutomaton,true);
				if (m_Pref.differenceSenwa()) {
					diff = new DifferenceSenwa<CodeBlock, IPredicate>(
							oldAbstraction, m_InterpolAutomaton, epd, false);
				} else {
					diff = new DifferenceDD<CodeBlock, IPredicate>(
							oldAbstraction, m_InterpolAutomaton, epd, 
							m_StateFactoryForRefinement,
							false, explointSigmaStarConcatOfIA);
				}
					s_Logger.info("Internal Transitions: " 
							+ epd.m_AnswerInternalAutomaton + " answers given by automaton " 
							+ epd.m_AnswerInternalCache + " answers given by cache " 
							+ epd.m_AnswerInternalSolver + " answers given by solver");
					s_Logger.info("Call Transitions: " 
							+ epd.m_AnswerCallAutomaton + " answers given by automaton " 
							+ epd.m_AnswerCallCache + " answers given by cache " 
							+ epd.m_AnswerCallSolver + " answers given by solver");
					s_Logger.info("Return Transitions: " 
							+ epd.m_AnswerReturnAutomaton + " answers given by automaton " 
							+ epd.m_AnswerReturnCache + " answers given by cache " 
							+ epd.m_AnswerReturnSolver + " answers given by solver");
				assert m_SmtManager.isIdle();
				assert (m_SmtManager.checkInductivity(m_InterpolAutomaton, false, true));
				// do the following check only to obtain logger messages of checkInductivity
				assert (m_SmtManager.checkInductivity(epd.getRejectionCache(), true, false) | true);
			break;
			
			case LAZYPOST:	
				PostDeterminizer lpd = new PostDeterminizer(m_SmtManager,	m_Pref, 
									m_InterpolAutomaton,false);
				if (m_Pref.differenceSenwa()) {
					diff = new DifferenceSenwa<CodeBlock, IPredicate>(
							oldAbstraction, m_InterpolAutomaton, lpd, false);
				} else {
					diff = new DifferenceDD<CodeBlock, IPredicate>(
							oldAbstraction, m_InterpolAutomaton, lpd, 
							m_StateFactoryForRefinement,
							false, explointSigmaStarConcatOfIA);
				}
				
					s_Logger.info("Internal Transitions: " 
							+ lpd.m_AnswerInternalAutomaton + " answers given by automaton " 
							+ lpd.m_AnswerInternalCache + " answers given by cache " 
							+ lpd.m_AnswerInternalSolver + " answers given by solver");
					s_Logger.info("Call Transitions: " 
							+ lpd.m_AnswerCallAutomaton+ " answers given by automaton " 
							+ lpd.m_AnswerCallCache+ " answers given by cache " 
							+ lpd.m_AnswerCallSolver+ " answers given by solver");
					s_Logger.info("Return Transitions: " 
							+ lpd.m_AnswerReturnAutomaton + " answers given by automaton " 
							+ lpd.m_AnswerReturnCache+ " answers given by cache " 
							+ lpd.m_AnswerReturnSolver+ " answers given by solver");
				assert m_SmtManager.isIdle();
				assert (m_SmtManager.checkInductivity(m_InterpolAutomaton, false, true));
				// do the following check only to obtain logger messages of checkInductivity
				assert (m_SmtManager.checkInductivity(lpd.getRejectionCache(), true, false) | true);
			break;
			
			case SELFLOOP:
				SelfloopDeterminizer sed = new SelfloopDeterminizer(
						m_SmtManager, m_Pref, m_InterpolAutomaton);
				if (m_Pref.differenceSenwa()) {
					diff = new DifferenceSenwa<CodeBlock, IPredicate>(
							oldAbstraction, m_InterpolAutomaton, sed, false);
				} else {
					diff = new DifferenceDD<CodeBlock, IPredicate>(
							oldAbstraction, m_InterpolAutomaton, sed, 
							m_StateFactoryForRefinement,
							false, explointSigmaStarConcatOfIA);
				}
				s_Logger.info("Internal Selfloops: "+ sed.m_InternalSelfloop 
						+ " Internal NonSelfloops " + sed.m_InternalNonSelfloop);
				s_Logger.info("Call Selfloops: " + sed.m_CallSelfloop 
						+ " Call NonSelfloops "+ sed.m_CallNonSelfloop);
				s_Logger.info("Return Selfloops: " + sed.m_ReturnSelfloop 
						+ " Return NonSelfloops "+ sed.m_ReturnNonSelfloop);
			break;
			case STRONGESTPOST:
				StrongestPostDeterminizer spd = new StrongestPostDeterminizer(
						m_SmtManager, m_Pref, m_InterpolAutomaton);
				if (m_Pref.differenceSenwa()) {
					diff = new DifferenceSenwa<CodeBlock, IPredicate>(
							oldAbstraction, m_InterpolAutomaton, spd, false);
				} else {
					diff = new DifferenceDD<CodeBlock, IPredicate>(
							oldAbstraction, m_InterpolAutomaton, spd, 
							m_StateFactoryForRefinement,
							false, explointSigmaStarConcatOfIA);
				}
			break;
			default:
				throw new UnsupportedOperationException();
			}
			if (m_RemoveDeadEnds && m_Pref.computeHoareAnnotation()) {
				m_Haf.wipeReplacedContexts();
				m_Haf.addDeadEndDoubleDeckers(diff);
			}
			if (m_RemoveDeadEnds) {
				diff.removeDeadEnds();
			}
				
				
			m_Abstraction = (IAutomaton<CodeBlock, IPredicate>) diff.getResult();
			m_DeadEndRemovalTime = diff.getDeadEndRemovalTime();
		}
		else {//complement and intersection instead of difference

			INestedWordAutomatonOldApi<CodeBlock, IPredicate> dia = 
											determinizeInterpolantAutomaton();			

			s_Logger.debug("Start complementation");
			INestedWordAutomatonOldApi<CodeBlock, IPredicate> nia = 
				(new ComplementDD<CodeBlock, IPredicate>(dia)).getResult();
			assert(!nia.accepts(m_Counterexample.getWord()));
			s_Logger.info("Complemented interpolant automaton has "+nia.size() +" states");
			
			if (m_Iteration <= m_Pref.watchIteration() && m_Pref.artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON) {
				m_ArtifactAutomaton = nia;
			}
			assert(oldAbstraction.getStateFactory() == m_InterpolAutomaton.getStateFactory());
			s_Logger.debug("Start intersection");
			IntersectDD<CodeBlock, IPredicate> intersect =
					new IntersectDD<CodeBlock, IPredicate>(
							false, oldAbstraction, nia);
			if (m_RemoveDeadEnds && m_Pref.computeHoareAnnotation()) {
				m_Haf.wipeReplacedContexts();
				m_Haf.addDeadEndDoubleDeckers(intersect);
			}
			if (m_RemoveDeadEnds) {
				intersect.removeDeadEnds();
			}
			m_Abstraction = intersect.getResult(); 
		}
		
//		if(m_RemoveDeadEnds && m_Pref.computeHoareAnnotation()) {
//			m_Haf.wipeReplacedContexts();
//			m_Haf.addDoubleDeckers(removedDoubleDeckers, oldAbstraction.getEmptyStackState());
//			m_Haf.addContext2Entry(context2entry);
//		}

		(new RemoveDeadEnds<CodeBlock, IPredicate>((INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction)).getResult();
		m_TimingStatistics.finishDifference();
		
		if (m_Pref.minimize()) {
			m_TimingStatistics.startAutomataMinimization();
			long startTime = System.currentTimeMillis();
			int oldSize = m_Abstraction.size();
			INestedWordAutomatonOldApi<CodeBlock, IPredicate> newAbstraction = (INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction;
			Collection<Set<IPredicate>> partition = computePartition(newAbstraction);
			MinimizeSevpa<CodeBlock, IPredicate> minimizeOp = new MinimizeSevpa<CodeBlock, IPredicate>(newAbstraction, partition, false, false, m_StateFactoryForRefinement);
			INestedWordAutomatonOldApi<CodeBlock, IPredicate> minimized = minimizeOp.getResult();
			if (m_Pref.computeHoareAnnotation()) {
				Map<IPredicate, IPredicate> oldState2newState = minimizeOp.getOldState2newState();
				m_Haf.updateContexts(oldState2newState);
			}
			int newSize = minimized.size();
			m_Abstraction = minimized;
			m_MinimizationTime += (System.currentTimeMillis() - startTime);
			if (oldSize != 0 && oldSize < newSize) {
				throw new AssertionError("Minimization increased state space");
			}
			m_StatesRemovedByMinimization += (oldSize - newSize);
			m_TimingStatistics.finishAutomataMinimization();
		}
		
		
//		MinimizeSevpa<CodeBlock, Predicate> sev = new MinimizeSevpa<CodeBlock, Predicate>(abstraction);
//		new MinimizeSevpa<CodeBlock, Predicate>.Partitioning(0);


//		 for (Predicate p : a.getStates()) {
//			 assert a.numberOfOutgoingInternalTransitions(p) <= 2 : p + " has " +a.numberOfOutgoingInternalTransitions(p);
//			 assert a.numberOfIncomingInternalTransitions(p) <= 25 : p + " has " +a.numberOfIncomingInternalTransitions(p);
//		 }
		
		if(m_Abstraction.accepts(m_Counterexample.getWord())) {
			return false;
		}else {
			return true;
		}

	}
	
	
	
	private Collection<Set<IPredicate>> computePartition(INestedWordAutomatonOldApi<CodeBlock, IPredicate> automaton) {
		s_Logger.info("Start computation of initial partition.");
		Collection<IPredicate> states = automaton.getStates();
		Map<ProgramPoint, Set<IPredicate>> pp2p = new HashMap<ProgramPoint, Set<IPredicate>>();
		for (IPredicate p : states) {
			ISLPredicate sp = (ISLPredicate) p;
			Set<IPredicate> statesWithSamePP = pp2p.get(sp.getProgramPoint());
			if (statesWithSamePP == null) {
				statesWithSamePP = new HashSet<IPredicate>();
				pp2p.put(sp.getProgramPoint(), statesWithSamePP);
			}
			statesWithSamePP.add(p);
		}
		Collection<Set<IPredicate>> partition = new ArrayList<Set<IPredicate>>();
		for (ProgramPoint pp : pp2p.keySet()) {
			Set<IPredicate> statesWithSamePP = pp2p.get(pp);
			partition.add(statesWithSamePP);
		}
		s_Logger.info("Finished computation of initial partition.");
		return partition;
	}
	
	private boolean eachStateIsFinal(Collection<IPredicate> states, INestedWordAutomatonOldApi<CodeBlock, IPredicate> automaton) {
		boolean result = true;
		for (IPredicate p : states) {
			result &= automaton.isFinal(p);
		}
		return result;
	}
	
	
	protected INestedWordAutomatonOldApi<CodeBlock, IPredicate> 
											determinizeInterpolantAutomaton() throws OperationCanceledException {
		s_Logger.debug("Start determinization");
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> dia;
		switch (m_Pref.determinization()) {
		case POWERSET: 
			PowersetDeterminizer<CodeBlock, IPredicate> psd = 
				new PowersetDeterminizer<CodeBlock, IPredicate>(m_InterpolAutomaton);
			DeterminizeDD<CodeBlock, IPredicate> dabps = 
				new DeterminizeDD<CodeBlock, IPredicate>(
												m_InterpolAutomaton, psd);
			dia = dabps.getResult();
		break;
		case BESTAPPROXIMATION:	
			BestApproximationDeterminizer bed = 
				new BestApproximationDeterminizer(m_SmtManager,	m_Pref, 
									m_InterpolAutomaton);
			DeterminizeDD<CodeBlock, IPredicate> dab = 
				new DeterminizeDD<CodeBlock, IPredicate>(
												m_InterpolAutomaton, bed);
			dia = dab.getResult();
		break;
		case SELFLOOP:
			SelfloopDeterminizer sed = 
				new SelfloopDeterminizer(m_SmtManager,	m_Pref, 
										m_InterpolAutomaton);
			DeterminizeDD<CodeBlock, IPredicate> dabsl = 
				new DeterminizeDD<CodeBlock, IPredicate>(
												m_InterpolAutomaton, sed);
			dia = dabsl.getResult();
		break;
		case STRONGESTPOST:
			StrongestPostDeterminizer spd = 
				new StrongestPostDeterminizer(m_SmtManager,	m_Pref, 
										m_InterpolAutomaton);
			DeterminizeDD<CodeBlock, IPredicate> dabsp = 
				new DeterminizeDD<CodeBlock, IPredicate>(
												m_InterpolAutomaton, spd);
			dia = dabsp.getResult();
		break;
		case EAGERPOST:
			PostDeterminizer epd = 
				new PostDeterminizer(m_SmtManager,	m_Pref, 
									m_InterpolAutomaton,true);
			DeterminizeDD<CodeBlock, IPredicate> dep = 
				new DeterminizeDD<CodeBlock, IPredicate>(
												m_InterpolAutomaton, epd);
			dia = dep.getResult();
		break;
		case LAZYPOST:
			PostDeterminizer lpd = 
				new PostDeterminizer(m_SmtManager,	m_Pref, 
									m_InterpolAutomaton,true);
			DeterminizeDD<CodeBlock, IPredicate> dlpd = 
				new DeterminizeDD<CodeBlock, IPredicate>(
												m_InterpolAutomaton, lpd);
			dia = dlpd.getResult();
		break;

		default:
			throw new UnsupportedOperationException();
		}
		
		if (m_Pref.computeHoareAnnotation()) {
			assert (m_SmtManager.checkInductivity(dia, false, true)) : "Not inductive";
		}
		if (m_Pref.dumpAutomata()) {
			String filename = m_Pref.dumpPath() + "/InterpolantAutomatonDeterminized_Iteration" + m_Iteration; 
			new AtsDefinitionPrinter<String,String>(filename, m_PrintAutomataLabeling, "",dia);
		}
		assert(dia.accepts(m_Counterexample.getWord()));
		s_Logger.debug("Sucessfully determinized");
		return dia;
	}
	
	
	
	
	@Override
	protected void computeCFGHoareAnnotation() {
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> abstraction = 
				(INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction;
		new HoareAnnotationExtractor(abstraction, m_Haf);
		m_Haf.addHoareAnnotationToCFG(m_SmtManager);
	}
	
	@Override
	public IElement getArtifact() {
		if (m_Pref.artifact() == Artifact.ABSTRACTION ||
				m_Pref.artifact() == Artifact.INTERPOLANT_AUTOMATON ||
				m_Pref.artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON) {
	
			if (m_ArtifactAutomaton == null) {
				s_Logger.warn("Preferred Artifact not available," +
				" visualizing the RCFG instead");
				return m_RootNode;
			}
			else {
				return Automaton2UltimateModel.ultimateModel(m_ArtifactAutomaton);
			}
		}
		else if (m_Pref.artifact() == Artifact.RCFG) {
			return m_RootNode;
		}
		else {
			throw new IllegalArgumentException();
		}
	}
	

	
	public void howDifferentAreInterpolants(Collection<IPredicate> predicates) {
		int implications = 0;
		int biimplications = 0; 
		IPredicate[] array = predicates.toArray(new IPredicate[0]);
		for (int i=0; i<array.length; i++) {
			for (int j=0; j<i; j++) {
				boolean implies = (m_SmtManager.isCovered(array[i], array[j]) == LBool.UNSAT);
				boolean explies = (m_SmtManager.isCovered(array[j], array[i]) == LBool.UNSAT);
				if (implies && explies) {
					biimplications++;
				} else if (implies ^ explies) {
					implications++;
				}
				
			}
		}
		s_Logger.warn(array.length + "Interpolants. " + implications 
				+ " implications " + biimplications + " biimplications");
	}
	



}
