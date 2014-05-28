package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.Automaton2UltimateModel;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.InCaReAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.ShrinkNwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.ComplementDD;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DeterminizeDD;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IntersectDD;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.senwa.DifferenceSenwa;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.BestApproximationDeterminizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.EagerInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.PostDeterminizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.SelfloopDeterminizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.StrongestPostDeterminizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantAutomataBuilders.CanonicalInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantAutomataBuilders.StraightLineInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantAutomataBuilders.TwoTrackInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker.AllIntegers;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerSpWp;

/**
 * Subclass of AbstractCegarLoop which provides all algorithms for checking
 * safety (not termination).
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BasicCegarLoop extends AbstractCegarLoop {
	
	private final static boolean differenceInsteadOfIntersection = true;
	
	protected final static boolean m_RemoveDeadEnds = true;

	
	protected HoareAnnotationFragments m_Haf;

	protected final PredicateFactoryRefinement m_StateFactoryForRefinement;
	protected final PredicateFactory m_PredicateFactoryInterpolantAutomata;
	protected final PredicateFactoryResultChecking m_PredicateFactoryResultChecking;
	
	
	
	protected final INTERPOLATION m_Interpolation;
	
	protected final boolean m_ComputeHoareAnnotation;
	
	public BasicCegarLoop(String name, RootNode rootNode,
			SmtManager smtManager,
			TAPreferences taPrefs,
			Collection<ProgramPoint> errorLocs,
			INTERPOLATION interpolation, boolean computeHoareAnnotation) {
	
		super(name, rootNode, smtManager, taPrefs, errorLocs);
		m_Interpolation = interpolation;
		m_ComputeHoareAnnotation = computeHoareAnnotation;
		m_Haf = new HoareAnnotationFragments();
		m_StateFactoryForRefinement = new PredicateFactoryRefinement(
				m_RootNode.getRootAnnot().getProgramPoints(),
				super.m_SmtManager,
				m_Pref,
				m_RemoveDeadEnds && m_ComputeHoareAnnotation,
				m_Haf);
		m_PredicateFactoryInterpolantAutomata = new PredicateFactory(
				super.m_SmtManager,
				m_Pref);
		m_PredicateFactoryResultChecking = new PredicateFactoryResultChecking(smtManager);
		m_CegarLoopBenchmark = new CegarLoopBenchmarkGenerator();
		m_CegarLoopBenchmark.start(CegarLoopBenchmarkType.s_OverallTime);
	}
	
	
	
	


	@Override
	protected void getInitialAbstraction() throws AutomataLibraryException {
		CFG2NestedWordAutomaton cFG2NestedWordAutomaton = 
			new CFG2NestedWordAutomaton(m_Pref, super.m_SmtManager);
		
		m_Abstraction = cFG2NestedWordAutomaton.getNestedWordAutomaton(
						super.m_RootNode, m_StateFactoryForRefinement, super.m_ErrorLocs);
	}
	
	
	
	
	
	@Override
	protected boolean isAbstractionCorrect() throws OperationCanceledException {			
		try {
			m_Counterexample = (new IsEmpty<CodeBlock,IPredicate>((INestedWordAutomatonOldApi) m_Abstraction)).getNestedRun();
		} catch (OperationCanceledException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		if (m_Counterexample == null) {
			return true;
		}
		else {
			if (m_Pref.dumpAutomata()) {
				dumpNestedRun(m_Counterexample, m_IterationPW);
			}
//			m_RunAnalyzer = new RunAnalyzer(m_Counterexample);
			s_Logger.info("Found potential Counterexample");
//			s_Logger.info("Cutpoints: " + m_RunAnalyzer.getCutpoints());
//			s_Logger.debug(m_RunAnalyzer.getOccurence());
			return false;
		}
	}
	
	

	
	@Override
	protected LBool isCounterexampleFeasible() {
		IPredicate truePredicate = m_SmtManager.newTruePredicate();
		IPredicate falsePredicate = m_SmtManager.newFalsePredicate();
		PredicateUnifier predicateUnifier = new PredicateUnifier(m_SmtManager,
				truePredicate, falsePredicate);
		switch (m_Interpolation) {
		case Craig_NestedInterpolation:
		case Craig_TreeInterpolation:
			m_TraceChecker = new TraceChecker(truePredicate, falsePredicate, 
					null, NestedWord.nestedWord(m_Counterexample.getWord()),m_SmtManager,
					m_RootNode.getRootAnnot().getModGlobVarManager());
			break;
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP:
			m_TraceChecker = new TraceCheckerSpWp(truePredicate, falsePredicate, 
					null, NestedWord.nestedWord(m_Counterexample.getWord()),m_SmtManager,
					m_RootNode.getRootAnnot().getModGlobVarManager());
			break;
		default:
			throw new UnsupportedOperationException("unsupported interpolation");
		}
		LBool feasibility = m_TraceChecker.isCorrect();
		if (feasibility != LBool.UNSAT) {
			s_Logger.info("Counterexample might be feasible");
			NestedWord<CodeBlock> counterexample = NestedWord.nestedWord(m_Counterexample.getWord());
			String indentation = "";
			indentation += "  ";
			for (int j=0; j < counterexample.length(); j++) {
				String stmts = counterexample.getSymbol(j).getPrettyPrintedStatements();
//				System.out.println(indentation + stmts);
//				s_Logger.info(indentation + stmts);
				if (counterexample.isCallPosition(j)) {
					indentation += "    "; 
				}
				if (counterexample.isReturnPosition(j)) {
					indentation = indentation.substring(0, indentation.length()-4); 
				}
			}
			m_TraceChecker.computeRcfgProgramExecution();
//			s_Logger.info("Trace with values");
//			s_Logger.info(m_TraceChecker.getRcfgProgramExecution());
			m_RcfgProgramExecution = m_TraceChecker.getRcfgProgramExecution();
		} else {
			AllIntegers allInt = new TraceChecker.AllIntegers();
			m_TraceChecker.computeInterpolants(allInt, predicateUnifier, m_Interpolation);
		}
		
		m_CegarLoopBenchmark.addTraceCheckerData(m_TraceChecker.getTraceCheckerBenchmark());
//		m_TraceCheckerBenchmark.aggregateBenchmarkData(m_TraceChecker.getTraceCheckerBenchmark());
		
		return feasibility;
	}
	
	
	private List<ProgramPoint> extractProgramPoints() {
		ArrayList<IPredicate> predicateSequence = ((NestedRun<CodeBlock, IPredicate>) m_Counterexample).getStateSequence();
		ArrayList<ProgramPoint> result = new ArrayList<>();
		for (IPredicate p : predicateSequence) {
			result.add(((ISLPredicate) p).getProgramPoint());
		}
		return result;
	}
	

	
	@Override
	protected void constructInterpolantAutomaton() throws OperationCanceledException {
		m_CegarLoopBenchmark.start(CegarLoopBenchmarkType.s_BasicInterpolantAutomatonTime);
		switch (m_Pref.interpolantAutomaton()) {
		case CANONICAL:
		{
			List<ProgramPoint> programPoints = extractProgramPoints();
			CanonicalInterpolantAutomatonBuilder iab = new CanonicalInterpolantAutomatonBuilder(
					m_TraceChecker, 
					programPoints, 
					new InCaReAlphabet<CodeBlock>(m_Abstraction), 
					m_SmtManager, 
					m_PredicateFactoryInterpolantAutomata);
			iab.analyze();
			m_InterpolAutomaton = iab.getInterpolantAutomaton();
			s_Logger.info("Interpolatants " + m_InterpolAutomaton.getStates());
			
//			m_CegarLoopBenchmark.addBackwardCoveringInformation(iab.getBackwardCoveringInformation());
			BackwardCoveringInformation bci = TraceCheckerUtils.computeCoverageCapability(m_TraceChecker, programPoints);
			m_CegarLoopBenchmark.addBackwardCoveringInformation(bci);
		}
		break;
		case SINGLETRACE:{
			StraightLineInterpolantAutomatonBuilder iab = 
					new StraightLineInterpolantAutomatonBuilder(
							new InCaReAlphabet<CodeBlock>(m_Abstraction),
							m_TraceChecker, m_PredicateFactoryInterpolantAutomata);
			m_InterpolAutomaton = iab.getResult();
		}
		break;
		case TOTALINTERPOLATION:
			throw new AssertionError("not supported by this CegarLoop");
		case TWOTRACK:
		{
			TwoTrackInterpolantAutomatonBuilder ttiab = 
					new TwoTrackInterpolantAutomatonBuilder(m_Counterexample,
							m_SmtManager, m_TraceChecker, m_Abstraction);
			m_InterpolAutomaton = ttiab.getResult();
		}
		break;
		}
		m_CegarLoopBenchmark.stop(CegarLoopBenchmarkType.s_BasicInterpolantAutomatonTime);
		assert(accepts(m_InterpolAutomaton, m_Counterexample.getWord())) :
			"Interpolant automaton broken!";
		assert (m_SmtManager.checkInductivity(m_InterpolAutomaton, false, true));
	}
	
	

	
	
	
	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		m_StateFactoryForRefinement.setIteration(super.m_Iteration);
//		howDifferentAreInterpolants(m_InterpolAutomaton.getStates());
		
		m_CegarLoopBenchmark.start(CegarLoopBenchmarkType.s_AutomataDifference);
		boolean explointSigmaStarConcatOfIA = !m_ComputeHoareAnnotation;
		
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> oldAbstraction = 
				(INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction;
		Map<IPredicate, Set<IPredicate>> removedDoubleDeckers = null;
		Map<IPredicate, IPredicate> context2entry = null;
		EdgeChecker edgeChecker = new EdgeChecker(m_SmtManager, 
				m_RootNode.getRootAnnot().getModGlobVarManager(),
				m_TraceChecker.getPredicateUnifier().getCoverageRelation());
		try {
			if (differenceInsteadOfIntersection) {
				s_Logger.debug("Start constructing difference");
//				assert(oldAbstraction.getStateFactory() == m_InterpolAutomaton.getStateFactory());
				
				IOpWithDelayedDeadEndRemoval<CodeBlock, IPredicate> diff;
				
				switch (m_Pref.determinization()) {
				case POWERSET:
					PowersetDeterminizer<CodeBlock, IPredicate> psd = 
						new PowersetDeterminizer<CodeBlock, IPredicate>(m_InterpolAutomaton, true, m_PredicateFactoryInterpolantAutomata);
					if (m_Pref.differenceSenwa()) {
						diff = new DifferenceSenwa<CodeBlock, IPredicate>(
									oldAbstraction, m_InterpolAutomaton, psd, false);
					} else {
						diff = new Difference<CodeBlock, IPredicate>(
								oldAbstraction, m_InterpolAutomaton, psd, 
								m_StateFactoryForRefinement,
								explointSigmaStarConcatOfIA);
					}
				break;
				case BESTAPPROXIMATION:	
					BestApproximationDeterminizer bed = 
						new BestApproximationDeterminizer(m_SmtManager,	m_Pref, 
												m_InterpolAutomaton, m_PredicateFactoryInterpolantAutomata);
					diff = new Difference<CodeBlock, IPredicate>(
								oldAbstraction, m_InterpolAutomaton, bed,
								m_StateFactoryForRefinement,
								explointSigmaStarConcatOfIA);
					
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
					PostDeterminizer epd = new PostDeterminizer(edgeChecker, m_ComputeHoareAnnotation, 
										m_InterpolAutomaton,true, m_PredicateFactoryInterpolantAutomata);
					if (m_Pref.differenceSenwa()) {
						diff = new DifferenceSenwa<CodeBlock, IPredicate>(
								oldAbstraction, m_InterpolAutomaton, epd, false);
					} else {
						diff = new Difference<CodeBlock, IPredicate>(
								oldAbstraction, m_InterpolAutomaton, epd, 
								m_StateFactoryForRefinement,
								explointSigmaStarConcatOfIA);
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
					PostDeterminizer lpd = new PostDeterminizer(edgeChecker,	m_ComputeHoareAnnotation, 
										m_InterpolAutomaton,false, m_PredicateFactoryInterpolantAutomata);
					if (m_Pref.differenceSenwa()) {
						diff = new DifferenceSenwa<CodeBlock, IPredicate>(
								oldAbstraction, m_InterpolAutomaton, lpd, false);
					} else {
						diff = new Difference<CodeBlock, IPredicate>(
								oldAbstraction, m_InterpolAutomaton, lpd, 
								m_StateFactoryForRefinement,
								explointSigmaStarConcatOfIA);
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
							m_SmtManager, m_Pref, m_InterpolAutomaton, m_PredicateFactoryInterpolantAutomata);
					if (m_Pref.differenceSenwa()) {
						diff = new DifferenceSenwa<CodeBlock, IPredicate>(
								oldAbstraction, m_InterpolAutomaton, sed, false);
					} else {
						diff = new Difference<CodeBlock, IPredicate>(
								oldAbstraction, m_InterpolAutomaton, sed, 
								m_StateFactoryForRefinement,
								explointSigmaStarConcatOfIA);
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
							edgeChecker, m_Pref, m_InterpolAutomaton, m_PredicateFactoryInterpolantAutomata);
					if (m_Pref.differenceSenwa()) {
						diff = new DifferenceSenwa<CodeBlock, IPredicate>(
								oldAbstraction, m_InterpolAutomaton, spd, false);
					} else {
						diff = new Difference<CodeBlock, IPredicate>(
								oldAbstraction, m_InterpolAutomaton, spd, 
								m_StateFactoryForRefinement,
								explointSigmaStarConcatOfIA);
					}
				break;
				case NEWEAGER:
					if (m_Pref.differenceSenwa()) {
						throw new UnsupportedOperationException();
					} else {
						EagerInterpolantAutomaton determinized = 
								new EagerInterpolantAutomaton(edgeChecker, m_InterpolAutomaton);
						PowersetDeterminizer<CodeBlock, IPredicate> psd2 = 
								new PowersetDeterminizer<CodeBlock, IPredicate>(determinized, true, m_PredicateFactoryInterpolantAutomata);
						diff = new Difference<CodeBlock, IPredicate>(
								oldAbstraction, determinized, psd2, 
								m_StateFactoryForRefinement,
								explointSigmaStarConcatOfIA);
						determinized.finishConstruction();
						assert(edgeChecker.isAssertionStackEmpty());
					}
					break;
				case CODENAME_PROJECT_BELLWALD:
					if (m_Pref.differenceSenwa()) {
						throw new UnsupportedOperationException();
					} else {
						DeterministicInterpolantAutomaton determinized = 
								new DeterministicInterpolantAutomaton(m_SmtManager, edgeChecker, oldAbstraction, m_InterpolAutomaton, m_TraceChecker);
//					ComplementDeterministicNwa<CodeBlock, IPredicate> cdnwa = new ComplementDeterministicNwa<>(dia);
						PowersetDeterminizer<CodeBlock, IPredicate> psd2 = 
								new PowersetDeterminizer<CodeBlock, IPredicate>(determinized, true, m_PredicateFactoryInterpolantAutomata);
						diff = new Difference<CodeBlock, IPredicate>(
								oldAbstraction, determinized, psd2, 
								m_StateFactoryForRefinement,
								explointSigmaStarConcatOfIA);
						determinized.finishConstruction();
						assert(edgeChecker.isAssertionStackEmpty());
						INestedWordAutomaton<CodeBlock, IPredicate> test = 
								(new RemoveUnreachable<CodeBlock, IPredicate>(determinized)).getResult();
//					boolean ctxAccepted = (new Accepts<CodeBlock, IPredicate>(
//							(INestedWordAutomatonOldApi<CodeBlock, IPredicate>) test, 
//							(NestedWord<CodeBlock>) m_Counterexample.getWord())).getResult();
//					if (!ctxAccepted) {
//						throw new AssertionError("counterexample not accepted by interpolant automaton");
//					}
						assert (m_SmtManager.checkInductivity(test, false, true));
					}
					break;
				default:
					throw new UnsupportedOperationException();
				}
				if (m_RemoveDeadEnds) {
					if (m_ComputeHoareAnnotation) {
						Difference<CodeBlock, IPredicate> difference = (Difference<CodeBlock, IPredicate>) diff;
						m_Haf.updateOnIntersection(difference.getFst2snd2res(), difference.getResult());
					}
					diff.removeDeadEnds();
					if (m_ComputeHoareAnnotation) {
						m_Haf.addDeadEndDoubleDeckers(diff);
					}
				}
					
					
				m_Abstraction = (IAutomaton<CodeBlock, IPredicate>) diff.getResult();
//				m_DeadEndRemovalTime = diff.getDeadEndRemovalTime();
				if (m_Pref.dumpAutomata()) {
					String filename = "InterpolantAutomaton_Iteration" + m_Iteration; 
					super.writeAutomatonToFile(m_InterpolAutomaton, filename);
				}
			}
			else {//complement and intersection instead of difference

				INestedWordAutomatonOldApi<CodeBlock, IPredicate> dia = 
												determinizeInterpolantAutomaton();			

				s_Logger.debug("Start complementation");
				INestedWordAutomatonOldApi<CodeBlock, IPredicate> nia = 
					(new ComplementDD<CodeBlock, IPredicate>(m_PredicateFactoryInterpolantAutomata, dia)).getResult();
				assert(!accepts(nia,m_Counterexample.getWord()));
				s_Logger.info("Complemented interpolant automaton has "+nia.size() +" states");
				
				if (m_Iteration <= m_Pref.watchIteration() && m_Pref.artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON) {
					m_ArtifactAutomaton = nia;
				}
				assert(oldAbstraction.getStateFactory() == m_InterpolAutomaton.getStateFactory());
				s_Logger.debug("Start intersection");
				IntersectDD<CodeBlock, IPredicate> intersect =
						new IntersectDD<CodeBlock, IPredicate>(
								false, oldAbstraction, nia);
				if (m_RemoveDeadEnds && m_ComputeHoareAnnotation) {
					throw new AssertionError("not supported any more");
					//m_Haf.wipeReplacedContexts();
					//m_Haf.addDeadEndDoubleDeckers(intersect);
				}
				if (m_RemoveDeadEnds) {
					intersect.removeDeadEnds();
				}
				m_Abstraction = intersect.getResult(); 
			}
		} finally {
			m_CegarLoopBenchmark.addEdgeCheckerData(edgeChecker.getEdgeCheckerBenchmark());
			m_CegarLoopBenchmark.stop(CegarLoopBenchmarkType.s_AutomataDifference);
		}
		
		
		
		
		
//		if(m_RemoveDeadEnds && m_ComputeHoareAnnotation) {
//			m_Haf.wipeReplacedContexts();
//			m_Haf.addDoubleDeckers(removedDoubleDeckers, oldAbstraction.getEmptyStackState());
//			m_Haf.addContext2Entry(context2entry);
//		}

//		(new RemoveDeadEnds<CodeBlock, IPredicate>((INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction)).getResult();
		
		
		Minimization minimization = m_Pref.minimize();
		switch (minimization) {
		case NONE:
			break;
		case MINIMIZE_SEVPA:
		case SHRINK_NWA:
			minimizeAbstraction(m_StateFactoryForRefinement, m_PredicateFactoryResultChecking, minimization);
			break;
		default:
			throw new AssertionError();
		}
		
//		MinimizeSevpa<CodeBlock, Predicate> sev = new MinimizeSevpa<CodeBlock, Predicate>(abstraction);
//		new MinimizeSevpa<CodeBlock, Predicate>.Partitioning(0);


//		 for (Predicate p : a.getStates()) {
//			 assert a.numberOfOutgoingInternalTransitions(p) <= 2 : p + " has " +a.numberOfOutgoingInternalTransitions(p);
//			 assert a.numberOfIncomingInternalTransitions(p) <= 25 : p + " has " +a.numberOfIncomingInternalTransitions(p);
//		 }
		boolean stillAccepted = (new Accepts<CodeBlock, IPredicate>(
				(INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction, 
				(NestedWord<CodeBlock>) m_Counterexample.getWord())).getResult();
		if(stillAccepted) {
			return false;
		}else {
			return true;
		}

	}




	/**
	 * Automata theoretic minimization of the automaton stored in m_Abstraction.
	 * Expects that m_Abstraction does not have dead ends.
	 * @param predicateFactoryRefinement PredicateFactory for the construction of the
	 * new (minimized) abstraction. 
	 * @param resultCheckPredFac PredicateFactory used for auxiliary automata
	 * used for checking correctness of the result (if assertions are enabled). 
	 */
	protected void minimizeAbstraction(PredicateFactory predicateFactoryRefinement,
			PredicateFactoryResultChecking resultCheckPredFac, Minimization minimization)
			throws OperationCanceledException, AutomataLibraryException,
			AssertionError {
		if (m_Pref.dumpAutomata()) {
			String filename = "AbstractionBeforeMinimization_Iteration" + m_Iteration; 
			super.writeAutomatonToFile(m_Abstraction, filename);
		}
		m_CegarLoopBenchmark.start(CegarLoopBenchmarkType.s_AutomataMinimizationTime);
		long startTime = System.currentTimeMillis();
		int oldSize = m_Abstraction.size();
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> newAbstraction = (INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction;
		Collection<Set<IPredicate>> partition = computePartition(newAbstraction);
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> minimized;
		try {
			switch (minimization) {
			case MINIMIZE_SEVPA:
			{
				MinimizeSevpa<CodeBlock, IPredicate> minimizeOp = new MinimizeSevpa<CodeBlock, IPredicate>(newAbstraction, partition, false, false, predicateFactoryRefinement);
				assert minimizeOp.checkResult(resultCheckPredFac);
				minimized = minimizeOp.getResult();
				if (m_ComputeHoareAnnotation) {
					Map<IPredicate, IPredicate> oldState2newState = minimizeOp.getOldState2newState();
					m_Haf.updateOnMinimization(oldState2newState, minimized);
				}
				break;
			}
			case SHRINK_NWA:
			{
				ShrinkNwa<CodeBlock, IPredicate> minimizeOp = new ShrinkNwa<CodeBlock, IPredicate>(
						predicateFactoryRefinement, newAbstraction, partition, true, false, false, 200, false, 0, false, false);
				assert minimizeOp.checkResult(resultCheckPredFac);
				minimized = (new RemoveUnreachable<CodeBlock, IPredicate>(minimizeOp.getResult())).getResult();
				if (m_ComputeHoareAnnotation) {
					Map<IPredicate, IPredicate> oldState2newState = minimizeOp.getOldState2newState();
					m_Haf.updateOnMinimization(oldState2newState, minimized);
				}
				break;
			}
			case NONE:
			default:
				throw new AssertionError();
			}
			int newSize = minimized.size();
			m_Abstraction = minimized;
			if (oldSize != 0 && oldSize < newSize) {
				throw new AssertionError("Minimization increased state space");
			}
			m_CegarLoopBenchmark.announceStatesRemovedByMinimization(oldSize - newSize);
		} finally {
			m_CegarLoopBenchmark.stop(CegarLoopBenchmarkType.s_AutomataMinimizationTime);
		}
	}
	
	
	







	private static Collection<Set<IPredicate>> computePartitionDistinguishFinalNonFinal(INestedWordAutomatonOldApi<CodeBlock, IPredicate> automaton) {
		s_Logger.info("Start computation of initial partition.");
		Collection<IPredicate> states = automaton.getStates();
		Map<ProgramPoint, Set<IPredicate>> pp2pFin = new HashMap<ProgramPoint, Set<IPredicate>>();
		Map<ProgramPoint, Set<IPredicate>> pp2pNonFin = new HashMap<ProgramPoint, Set<IPredicate>>();
		for (IPredicate p : states) {
			ISLPredicate sp = (ISLPredicate) p;
			if (automaton.isFinal(sp)) {
				pigeonHole(pp2pFin, sp);
			} else {
				pigeonHole(pp2pNonFin, sp);
			}

		}
		Collection<Set<IPredicate>> partition = new ArrayList<Set<IPredicate>>();
		for (ProgramPoint pp : pp2pFin.keySet()) {
			Set<IPredicate> statesWithSamePP = pp2pFin.get(pp);
			partition.add(statesWithSamePP);
		}
		for (ProgramPoint pp : pp2pNonFin.keySet()) {
			Set<IPredicate> statesWithSamePP = pp2pNonFin.get(pp);
			partition.add(statesWithSamePP);
		}
		s_Logger.info("Finished computation of initial partition.");
		return partition;
	}

	protected Collection<Set<IPredicate>> computePartition(INestedWordAutomatonOldApi<CodeBlock, IPredicate> automaton) {
		s_Logger.info("Start computation of initial partition.");
		Collection<IPredicate> states = automaton.getStates();
		Map<ProgramPoint, Set<IPredicate>> pp2p = new HashMap<ProgramPoint, Set<IPredicate>>();
		for (IPredicate p : states) {
			ISLPredicate sp = (ISLPredicate) p;
			pigeonHole(pp2p, sp);
		}
		Collection<Set<IPredicate>> partition = new ArrayList<Set<IPredicate>>();
		for (ProgramPoint pp : pp2p.keySet()) {
			Set<IPredicate> statesWithSamePP = pp2p.get(pp);
			partition.add(statesWithSamePP);
		}
		s_Logger.info("Finished computation of initial partition.");
		return partition;
	}


	/**
	 * Pigeon-hole (german: einsortieren) predicates according to their ProgramPoint
	 */
	private static void pigeonHole(Map<ProgramPoint, Set<IPredicate>> pp2p,
			ISLPredicate sp) {
		Set<IPredicate> statesWithSamePP = pp2p.get(sp.getProgramPoint());
		if (statesWithSamePP == null) {
			statesWithSamePP = new HashSet<IPredicate>();
			pp2p.put(sp.getProgramPoint(), statesWithSamePP);
		}
		statesWithSamePP.add(sp);
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
		EdgeChecker edgeChecker = new EdgeChecker(m_SmtManager, 
				m_RootNode.getRootAnnot().getModGlobVarManager());
		s_Logger.debug("Start determinization");
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> dia;
		switch (m_Pref.determinization()) {
		case POWERSET: 
			PowersetDeterminizer<CodeBlock, IPredicate> psd = 
				new PowersetDeterminizer<CodeBlock, IPredicate>(m_InterpolAutomaton, true, m_PredicateFactoryInterpolantAutomata);
			DeterminizeDD<CodeBlock, IPredicate> dabps = 
				new DeterminizeDD<CodeBlock, IPredicate>(
												m_InterpolAutomaton, psd);
			dia = dabps.getResult();
		break;
		case BESTAPPROXIMATION:	
			BestApproximationDeterminizer bed = 
				new BestApproximationDeterminizer(m_SmtManager,	m_Pref, 
									m_InterpolAutomaton, m_PredicateFactoryInterpolantAutomata);
			DeterminizeDD<CodeBlock, IPredicate> dab = 
				new DeterminizeDD<CodeBlock, IPredicate>(
												m_InterpolAutomaton, bed);
			dia = dab.getResult();
		break;
		case SELFLOOP:
			SelfloopDeterminizer sed = 
				new SelfloopDeterminizer(m_SmtManager,	m_Pref, 
										m_InterpolAutomaton, m_PredicateFactoryInterpolantAutomata);
			DeterminizeDD<CodeBlock, IPredicate> dabsl = 
				new DeterminizeDD<CodeBlock, IPredicate>(
												m_InterpolAutomaton, sed);
			dia = dabsl.getResult();
		break;
		case STRONGESTPOST:
			StrongestPostDeterminizer spd = 
				new StrongestPostDeterminizer(edgeChecker,	m_Pref, 
										m_InterpolAutomaton, m_PredicateFactoryInterpolantAutomata);
			DeterminizeDD<CodeBlock, IPredicate> dabsp = 
				new DeterminizeDD<CodeBlock, IPredicate>(
												m_InterpolAutomaton, spd);
			dia = dabsp.getResult();
		break;
		case EAGERPOST:
			PostDeterminizer epd = 
				new PostDeterminizer(edgeChecker,	m_ComputeHoareAnnotation, 
									m_InterpolAutomaton,true, m_PredicateFactoryInterpolantAutomata);
			DeterminizeDD<CodeBlock, IPredicate> dep = 
				new DeterminizeDD<CodeBlock, IPredicate>(
												m_InterpolAutomaton, epd);
			dia = dep.getResult();
		break;
		case LAZYPOST:
			PostDeterminizer lpd = 
				new PostDeterminizer(edgeChecker,	m_ComputeHoareAnnotation, 
									m_InterpolAutomaton,true, m_PredicateFactoryInterpolantAutomata);
			DeterminizeDD<CodeBlock, IPredicate> dlpd = 
				new DeterminizeDD<CodeBlock, IPredicate>(
												m_InterpolAutomaton, lpd);
			dia = dlpd.getResult();
		break;

		default:
			throw new UnsupportedOperationException();
		}
		
		if (m_ComputeHoareAnnotation) {
			assert (m_SmtManager.checkInductivity(dia, false, true)) : "Not inductive";
		}
		if (m_Pref.dumpAutomata()) {
			String filename = "InterpolantAutomatonDeterminized_Iteration" + m_Iteration; 
			writeAutomatonToFile(dia, filename);
		}
		assert(accepts(dia, m_Counterexample.getWord()));
		s_Logger.debug("Sucessfully determinized");
		return dia;
	}
	
	
	
	
	@Override
	protected void computeCFGHoareAnnotation() {
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> abstraction = 
				(INestedWordAutomatonOldApi<CodeBlock, IPredicate>) m_Abstraction;
		new HoareAnnotationExtractor(abstraction, m_Haf);
		(new HoareAnnotationWriter(m_RootNode.getRootAnnot(), m_SmtManager, m_Haf)).addHoareAnnotationToCFG();;
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
				try {
					return Automaton2UltimateModel.ultimateModel(m_ArtifactAutomaton);
				} catch (OperationCanceledException e) {
					return null;
				}
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
	

	
	protected static boolean accepts(
			INestedWordAutomaton<CodeBlock, IPredicate> nia,
			Word<CodeBlock> word) throws OperationCanceledException {
		return (new Accepts<CodeBlock, IPredicate>(nia, NestedWord.nestedWord(word), false, false)).getResult();
	}


	public CegarLoopBenchmarkGenerator getCegarLoopBenchmark() {
		return m_CegarLoopBenchmark;
	}
	
	
	
	


}
