package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter.Labeling;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiComplementFKV;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiDifferenceFKV;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiIntersect;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveNonLiveStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DifferenceDD;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.RankingFunctionsObserver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.RankingFunctionsSynthesizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.SupportingInvariant;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.TermIsNotAffineException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.functions.LinearRankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.functions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.templates.LinearTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceValues.Solver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CFG2NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.HoareAnnotationFragments;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.PostDeterminizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker.AllIntegers;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.RankingFunctionResult;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;

public class BuchiCegarLoop {
	protected final static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
		
		/**
		 * Result of CEGAR loop iteration <ul>
		 * <li> SAFE: there is no feasible trace to an error location
		 * <li> UNSAFE: there is a feasible trace to an error location 
		 * (the underlying program has at least one execution which violates its 
		 * specification)
		 * <li> UNKNOWN: we found a trace for which we could not decide feasibility
		 * or we found an infeasible trace but were not able to exclude it in 
		 * abstraction refinement.
		 * <li> TIMEOUT: 
		 */
		public enum Result { TERMINATING, TIMEOUT , UNKNOWN }
		
		
		private final String m_Name;
		
		/**
		 * Node of a recursive control flow graph which stores additional 
		 * information about the 
		 */
		protected final RootNode m_RootNode;
		
		
		/**
		 * Intermediate layer to encapsulate communication with SMT solvers. 
		 */
		protected final SmtManager m_SmtManager;
		
		
		/**
		 * Intermediate layer to encapsulate preferences.
		 */
		protected final TAPreferences m_Pref;
		
		/**
		 * Current Iteration of this CEGAR loop.
		 */
		protected int m_Iteration = 0;
		
		
		/**
		 * Accepting run of the abstraction obtained in this iteration. 
		 */
		protected NestedLassoRun<CodeBlock, IPredicate> m_Counterexample;
		
		
		/**
		 * Abstraction of this iteration. The language of m_Abstraction is a set
		 * of traces which is <ul>
		 * <li> a superset of the feasible program traces.
		 * <li> a subset of the traces which respect the control flow of of the
		 * program.
		 */
		protected INestedWordAutomatonOldApi<CodeBlock, IPredicate> m_Abstraction;
		
		
		/**
		 * TraceChecker of this iteration.
		 */
		protected TraceChecker m_TraceChecker;
		

		/**
		 * Interpolant automaton of this iteration.
		 */
		protected NestedWordAutomaton<CodeBlock, IPredicate> m_InterpolAutomaton;
		
		private final BinaryStatePredicateManager m_Bspm;
		
		protected IAutomaton<CodeBlock, IPredicate> m_ArtifactAutomaton;
		
		// used for the collection of statistics
		public int m_BiggestAbstractionIteration = 0;
		public int m_BiggestAbstractionSize = 0;
		public int m_InitialAbstractionSize = 0;
		
		int m_Infeasible = 0;
		int m_RankWithoutSi = 0;
		int m_RankWithSi = 0;

		private NestedRun<CodeBlock, IPredicate> m_ConcatenatedCounterexample;
		
		private LinearRankingFunction m_LinRf;

		private IPredicate m_TruePredicate;

		private IPredicate m_FalsePredicate;

		private Collection<SupportingInvariant> m_SiList;

		private PredicateFactory defaultStateFactory;

		private HoareAnnotationFragments m_Haf;

		private PredicateFactoryRefinement m_StateFactoryForRefinement;

		private BuchiModGlobalVarManager buchiModGlobalVarManager;

		

		private static final boolean m_ReduceAbstractionSize = true;
		private static final boolean m_Eager = true;
		private static final boolean m_Difference = true;
		private static final boolean m_UseDoubleDeckers = !true;

		public BuchiCegarLoop(RootNode rootNode,
				SmtManager smtManager,
				TAPreferences taPrefs) {
			this.m_Name = "BuchiCegarLoop";
			this.m_RootNode = rootNode;
			this.m_SmtManager = smtManager;
			this.m_Bspm = new BinaryStatePredicateManager(smtManager, 
					m_RootNode.getRootAnnot().getBoogie2SMT());
			this.buchiModGlobalVarManager = new BuchiModGlobalVarManager(
					m_Bspm.getUnseededVariable(), m_Bspm.getOldRankVariable(), 
					m_RootNode.getRootAnnot().getModGlobVarManager(),
					m_RootNode.getRootAnnot().getBoogie2SMT());

			this.m_Pref = taPrefs;
			defaultStateFactory = new PredicateFactory(
					m_SmtManager,
					m_Pref);
			
			m_Haf = new HoareAnnotationFragments(rootNode.getRootAnnot(),m_SmtManager);
			m_StateFactoryForRefinement = new PredicateFactoryRefinement(
					m_RootNode.getRootAnnot().getProgramPoints(),
					m_SmtManager,
					m_Pref,
					false && m_Pref.computeHoareAnnotation(),
					m_Haf);
		}
		
		NestedLassoRun<CodeBlock, IPredicate> getCounterexample() {
			return m_Counterexample;
		}
		
		
		
		public final Result iterate() {
			s_Logger.info("Interprodecural is " + m_Pref.interprocedural());		
			s_Logger.info("Solver is " + m_Pref.solver());
			s_Logger.info("Hoare is " + m_Pref.computeHoareAnnotation());
			s_Logger.info("Compute interpolants for " + m_Pref.interpolatedLocs());
			s_Logger.info("Backedges2True is " + m_Pref.edges2True());
			s_Logger.info("Backedges is " + m_Pref.interpolantAutomaton());
			s_Logger.info("Determinization is " + m_Pref.determinization());
			s_Logger.info("Difference is " + m_Pref.differenceSenwa());
			s_Logger.info("Minimize is " + m_Pref.minimize());

			
			m_Iteration = 0;
			s_Logger.info("======== Iteration " + m_Iteration + "==of CEGAR loop == " + m_Name + "========");
			
//			try {
				getInitialAbstraction();
//			} catch (OperationCanceledException e1) {
//				s_Logger.warn("Verification cancelled");
//				return Result.TIMEOUT;
//			}
			
			
			if (m_Iteration <= m_Pref.watchIteration() && 
					(m_Pref.artifact() == Artifact.ABSTRACTION || m_Pref.artifact() == Artifact.RCFG)) {
				m_ArtifactAutomaton = m_Abstraction;
			}
			if (m_Pref.dumpAutomata()) {
				String filename = m_Name+"Abstraction"+m_Iteration;
				writeAutomatonToFile(m_Abstraction, filename);
			}
			m_InitialAbstractionSize = m_Abstraction.size();
			m_BiggestAbstractionSize = m_Abstraction.size();
			
			
			
			boolean initalAbstractionCorrect;
			try {
				initalAbstractionCorrect = isAbstractionCorrect();
			} catch (OperationCanceledException e1) {
				s_Logger.warn("Verification cancelled");
				return Result.TIMEOUT;
			}
			if (initalAbstractionCorrect) {
				return Result.TERMINATING;
			}
			
			
			
			for (m_Iteration=1; m_Iteration<=m_Pref.maxIterations(); m_Iteration++){
				s_Logger.info("======== Iteration " + m_Iteration + "============");
				m_SmtManager.setIteration(m_Iteration);

				boolean abstractionCorrect;
				try {
					abstractionCorrect = isAbstractionCorrect();
				} catch (OperationCanceledException e1) {
					s_Logger.warn("Verification cancelled");
					return Result.TIMEOUT;
				}
				if (abstractionCorrect) {
					return Result.TERMINATING;
				}
				
				try {
					LBool isCounterexampleFeasible = isCounterexampleFeasible();
					if (isCounterexampleFeasible == Script.LBool.UNSAT) {
						refineFinite();
						m_Infeasible++;
					} else if (isCounterexampleFeasible == Script.LBool.SAT) {
						m_TraceChecker.forgetTrace();
						boolean terminating = isCounterexampleTerminating(
								m_Counterexample.getStem().getWord(), m_Counterexample.getLoop().getWord());
						if (!terminating) {
							return Result.UNKNOWN;
						} else {
							m_ConcatenatedCounterexample = null;
							refineBuchi();
						}
					} else {
						throw new AssertionError();
					}

					s_Logger.info("Abstraction has " + m_Abstraction.sizeInformation());
					s_Logger.info("Interpolant automaton has " + m_InterpolAutomaton.sizeInformation());
					
					if (m_ReduceAbstractionSize ) {
						m_Abstraction = (new RemoveNonLiveStates<CodeBlock, IPredicate>(m_Abstraction)).getResult();
						s_Logger.info("Abstraction has " + m_Abstraction.sizeInformation());
						Collection<Set<IPredicate>> partition = BuchiCegarLoop.computePartition(m_Abstraction);
						MinimizeSevpa<CodeBlock, IPredicate> minimizeOp = 
								new MinimizeSevpa<CodeBlock, IPredicate>(m_Abstraction, partition, false, false, m_StateFactoryForRefinement);
						minimizeOp.checkResult(defaultStateFactory);
						INestedWordAutomatonOldApi<CodeBlock, IPredicate> minimized = minimizeOp.getResult();
						if (m_Pref.computeHoareAnnotation()) {
							Map<IPredicate, IPredicate> oldState2newState = minimizeOp.getOldState2newState();
							m_Haf.updateContexts(oldState2newState);
						}
						m_Abstraction = minimized;
						s_Logger.info("Abstraction has " + m_Abstraction.sizeInformation());
					}


					if (m_Pref.computeHoareAnnotation()) {
						assert (m_SmtManager.checkInductivity(m_Abstraction, false, true));
					}

					if (m_Iteration <= m_Pref.watchIteration() && m_Pref.artifact() == Artifact.ABSTRACTION) {
						m_ArtifactAutomaton = m_Abstraction;
					}

					if (m_Pref.dumpAutomata()) {
						String filename = "Abstraction"+m_Iteration;
						writeAutomatonToFile(m_Abstraction, filename);
					}

					if (m_BiggestAbstractionSize < m_Abstraction.size()){
						m_BiggestAbstractionSize = m_Abstraction.size();
						m_BiggestAbstractionIteration = m_Iteration;
					}
				
				} catch (AutomataLibraryException e) {
					return Result.TIMEOUT;
				}
				m_TraceChecker = null;
				m_InterpolAutomaton = null;
				
			}
			return Result.TIMEOUT;
		}


		private boolean isAbstractionCorrect() throws OperationCanceledException {
			BuchiIsEmpty<CodeBlock, IPredicate> ec = new BuchiIsEmpty<CodeBlock, IPredicate>(m_Abstraction);
			if (ec.getResult()) {
				return true;
			} else {
				m_Counterexample = ec.getAcceptingNestedLassoRun();
				return false;
			}
		}


		private void getInitialAbstraction() {
			CFG2NestedWordAutomaton cFG2NestedWordAutomaton = 
					new CFG2NestedWordAutomaton(m_Pref,m_SmtManager);
			Collection<ProgramPoint> allpp = new HashSet<ProgramPoint>();
			for (Map<String, ProgramPoint> test : m_RootNode.getRootAnnot().getProgramPoints().values()) {
				allpp.addAll(test.values());
			}
			m_Abstraction = cFG2NestedWordAutomaton.getNestedWordAutomaton(
					m_RootNode, defaultStateFactory, allpp);
		}
		
		
		private LBool isCounterexampleFeasible() {
			assert m_ConcatenatedCounterexample == null;
			assert m_TraceChecker == null;
			NestedRun<CodeBlock, IPredicate> stem = m_Counterexample.getStem();
			s_Logger.info("Stem: " + stem);
			NestedRun<CodeBlock, IPredicate> loop = m_Counterexample.getLoop();
			s_Logger.info("Loop: " + loop);
			m_TraceChecker = new TraceChecker(m_SmtManager,
					m_RootNode.getRootAnnot().getModGlobVarManager(),
					m_RootNode.getRootAnnot().getEntryNodes(),
					null);
			m_TruePredicate = m_SmtManager.newTruePredicate();
			m_FalsePredicate = m_SmtManager.newFalsePredicate();
			
			LBool feasibility;
			m_ConcatenatedCounterexample = stem;
			feasibility = m_TraceChecker.checkTrace(m_TruePredicate, 
					m_FalsePredicate, m_ConcatenatedCounterexample.getWord());
			if (feasibility == LBool.UNSAT) {
				s_Logger.info("stem already infeasible");
			} else {
				m_TraceChecker.forgetTrace();
				m_ConcatenatedCounterexample = loop;
				feasibility = m_TraceChecker.checkTrace(m_TruePredicate, 
						m_FalsePredicate, m_ConcatenatedCounterexample.getWord());
				if (feasibility == LBool.UNSAT) {
					s_Logger.info("loop already infeasible");
				} else {
					m_TraceChecker.forgetTrace();
					m_ConcatenatedCounterexample = stem.concatenate(loop);
					feasibility = m_TraceChecker.checkTrace(m_TruePredicate, 
							m_FalsePredicate, m_ConcatenatedCounterexample.getWord());

				}
			}
			return feasibility;
		}
		
		private void refineFinite() throws OperationCanceledException {
			AllIntegers allInt = new TraceChecker.AllIntegers();
			IPredicate[] interpolants = m_TraceChecker.getInterpolants(allInt);
			constructInterpolantAutomaton(interpolants);
			EdgeChecker ec = new EdgeChecker(m_SmtManager, buchiModGlobalVarManager);
			PostDeterminizer spd = new PostDeterminizer(
					ec, m_Pref, m_InterpolAutomaton, false);
			DifferenceDD<CodeBlock, IPredicate> diff = null;
			try {
				diff = new DifferenceDD<CodeBlock, IPredicate>(
						m_Abstraction, m_InterpolAutomaton, spd, 
						m_StateFactoryForRefinement,
						false, true);
			} catch (AutomataLibraryException e) {
				if (e instanceof OperationCanceledException) {
					throw (OperationCanceledException) e;
				} else {
					throw new AssertionError();
				}
			}
			assert (new InductivityCheck(m_InterpolAutomaton, ec, false, true)).getResult();
			m_Abstraction = diff.getResult();
			m_ConcatenatedCounterexample = null;
		}
		
		protected void constructInterpolantAutomaton(IPredicate[] interpolants) throws OperationCanceledException {
			InterpolantAutomataBuilder iab = new InterpolantAutomataBuilder(
							m_ConcatenatedCounterexample,
							m_TruePredicate,
							m_FalsePredicate,
							interpolants,
							m_Pref.interpolantAutomaton(), m_Pref.edges2True(),
							m_SmtManager, m_Pref,
							m_Iteration, null);
			m_InterpolAutomaton = iab.buildInterpolantAutomaton(
					m_Abstraction, m_Abstraction.getStateFactory());
			
			assert((new Accepts<CodeBlock, IPredicate>(m_InterpolAutomaton, m_ConcatenatedCounterexample.getWord())).getResult()) :
				"Interpolant automaton broken!";
			assert((new BuchiAccepts<CodeBlock, IPredicate>(m_InterpolAutomaton, m_Counterexample.getNestedLassoWord())).getResult()) :
				"Interpolant automaton broken!";
			assert (m_SmtManager.checkInductivity(m_InterpolAutomaton, false, true));
		}
		
		
		
		boolean isCounterexampleTerminating(NestedWord<CodeBlock> stem, NestedWord<CodeBlock> loop) {
			CodeBlock[] stemCBs = new CodeBlock[stem.length()];
			for (int i=0; i<stem.length(); i++) {
				stemCBs[i] = stem.getSymbol(i);
			}
			CodeBlock[] loopCBs = new CodeBlock[loop.length()];
			for (int i=0; i<loop.length(); i++) {
				loopCBs[i] = loop.getSymbol(i);
			}
			@SuppressWarnings("deprecation")
			TransFormula stemTF = SequentialComposition.getInterproceduralTransFormula(
					m_RootNode.getRootAnnot().getBoogie2SMT(),
					m_RootNode.getRootAnnot().getModGlobVarManager(),
					m_RootNode.getRootAnnot().getTaPrefs().SimplifyCodeBlocks(), false, stemCBs);
			int stemVars = stemTF.getFormula().getFreeVars().length;

			@SuppressWarnings("deprecation")
			TransFormula loopTF = SequentialComposition.getInterproceduralTransFormula(
					m_RootNode.getRootAnnot().getBoogie2SMT(),
					m_RootNode.getRootAnnot().getModGlobVarManager(),
					m_RootNode.getRootAnnot().getTaPrefs().SimplifyCodeBlocks(),false, loopCBs);
			int loopVars = loopTF.getFormula().getFreeVars().length;
			s_Logger.info("Statistics: stemVars: " + stemVars + "loopVars: " + loopVars);
			{
				List<CodeBlock> composedCB = new ArrayList<CodeBlock>();
				composedCB.addAll(Arrays.asList(stemCBs));
				composedCB.addAll(Arrays.asList(loopCBs));
//				composedCB.addAll(Arrays.asList(loopCBs));
				TransFormula composed = SequentialComposition.getInterproceduralTransFormula(
						m_RootNode.getRootAnnot().getBoogie2SMT(),
						m_RootNode.getRootAnnot().getModGlobVarManager(),
						false, m_RootNode.getRootAnnot().getTaPrefs().SimplifyCodeBlocks(), composedCB.toArray(new CodeBlock[0])); 
						//TransFormula.sequentialComposition(10000, rootAnnot.getBoogie2SMT(), stemTF, loopTF);
				if (composed.isInfeasible() == Infeasibility.INFEASIBLE) {
					throw new AssertionError("suddently infeasible");
				}
			}
			NestedWord<CodeBlock> emptyWord = new NestedWord<CodeBlock>();
			IPredicate hondaPredicate = m_Counterexample.getLoop().getStateAtPosition(0);
			ProgramPoint honda = ((ISLPredicate) hondaPredicate).getProgramPoint();
			boolean withoutStem = synthesize(emptyWord, loop, getDummyTF(), loopTF);
			if (withoutStem) {
				m_RankWithoutSi++;
				reportRankingFunction(m_LinRf, honda, stem, loop);
				return true;
			}
			boolean witStem = synthesize(stem, loop, stemTF, loopTF);
			if (witStem) {
				reportRankingFunction(m_LinRf, honda, stem, loop);
				m_RankWithSi++;
				return true;
			}
			return false;
		}


		private	TransFormula getDummyTF() {
			Term term = m_SmtManager.getScript().term("true");
			Map<BoogieVar,TermVariable> inVars = new HashMap<BoogieVar,TermVariable>();
			Map<BoogieVar,TermVariable> outVars = new HashMap<BoogieVar,TermVariable>();
			Set<TermVariable> auxVars = new HashSet<TermVariable>();
			Set<TermVariable> branchEncoders = new HashSet<TermVariable>();
			Infeasibility infeasibility = Infeasibility.UNPROVEABLE;
			Term closedFormula = term;
			return new TransFormula(term, inVars, outVars, auxVars, branchEncoders, 
					infeasibility, closedFormula);
		}
		
		
		private void reportRankingFunction(LinearRankingFunction m_LinRf2,
				ProgramPoint honda, NestedWord<CodeBlock> stem,
				NestedWord<CodeBlock> loop) {
			Expression rfExp = m_LinRf.asExpression(m_SmtManager.getScript(),
					m_SmtManager.getBoogieVar2SmtVar());
			String rfString = RankingFunctionsObserver
					.backtranslateExprWorkaround(rfExp);
			StringBuilder longDescr = new StringBuilder();
			longDescr.append("Derived linear ranking function ");
			longDescr.append(rfString);
			longDescr.append(System.getProperty("line.separator"));
			longDescr.append(" with linear supporting invariants");
			for (SupportingInvariant si : m_SiList) {
				Expression siExp = si.asExpression(m_SmtManager.getScript(),
						m_SmtManager.getBoogieVar2SmtVar());
				String siString = RankingFunctionsObserver
						.backtranslateExprWorkaround(siExp);
				longDescr.append(" " + siString);
			}
			longDescr.append(System.getProperty("line.separator"));
			longDescr.append("For the following lasso. ");
			longDescr.append(System.getProperty("line.separator"));
			longDescr.append("Stem: ");
			longDescr.append(stem);
			longDescr.append(System.getProperty("line.separator"));
			longDescr.append("Loop: ");
			longDescr.append(loop);
			longDescr.append(System.getProperty("line.separator"));
			longDescr.append("length stem: " + stem.length()
					+ " length loop: " + loop.length());
			s_Logger.info(longDescr);
			IResult reportRes= new RankingFunctionResult<RcfgElement>(honda, 
					Activator.s_PLUGIN_ID, 
					UltimateServices.getInstance().getTranslatorSequence(), 
					honda.getPayload().getLocation(), 
					"Derived linear ranking function", 
					longDescr.toString());
			BuchiAutomizerObserver.reportResult(reportRes);
		}
		
		private boolean synthesize(NestedWord<CodeBlock> stem, NestedWord<CodeBlock> loop, TransFormula stemTF, TransFormula loopTF) {
			RankingFunctionsSynthesizer synthesizer = null;
			try {
				synthesizer = new RankingFunctionsSynthesizer(
						m_SmtManager.getScript(), new_Script(false), stemTF,
						loopTF);
			} catch (Exception e1) {
				e1.printStackTrace();
				throw new AssertionError(e1);
			}
			boolean found = false;
			try {
				found = synthesizer.synthesize(LinearTemplate.class);
				if (found) {
					RankingFunction rf = synthesizer.getRankingFunction();
					assert (rf != null);
					m_SiList = synthesizer.getSupportingInvariants();
					assert (m_SiList != null);
					m_LinRf = (LinearRankingFunction) rf;
					m_Bspm.computePredicates(m_LinRf, m_SiList);
					
					for (SupportingInvariant si : m_SiList) {
						if (stem.length() > 0) {
							assert m_Bspm.checkSupportingInvariant(
									si, stem, loop, m_RootNode.getRootAnnot()) : 
									"Wrong supporting invariant " + si;
						}
					}
//					boolean correctWithoutSi = checkRankDecrease();
//					if (correctWithoutSi) {
//						s_Logger.info("Statistics: For this ranking function no si needed");
//					} else {
//						s_Logger.info("Statistics: We need si for this ranking function");
//					}
					assert m_Bspm.checkRankDecrease(loop, m_RootNode.getRootAnnot()) : 
						"Wrong ranking function " + rf;

				} else {
//					s_Logger.info("Statistics: No ranking function has been found "
//							+ "with this template.");
				}
			} catch (SMTLIBException e) {
				throw new AssertionError(e.getMessage());
			} catch (TermIsNotAffineException e) {
				throw new AssertionError(e.getMessage());
			} catch (InstantiationException e) {
				throw new AssertionError(e.getMessage());
			} catch (AssertionError e) {
				throw new AssertionError(e.getMessage());
			}
			return found;
		}
		
		Script new_Script(boolean nonlinear) {
			// This code is essentially copied from 
			// de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CfgBuilder
			// since there is no obvious way to implement it as shared code.
			
			TAPreferences taPref = new TAPreferences();
			Logger solverLogger = Logger.getLogger("interpolLogger");
			Script script;
			
			if (taPref.solver() == Solver.SMTInterpol) {
				script = new SMTInterpol(solverLogger,false);
			} else if (taPref.solver() == Solver.Z3) {
				script = new Scriptor("z3 -smt2 -in", solverLogger);
			} else {
				throw new AssertionError();
			}
			
			if (taPref.dumpScript()) {
				String dumpFileName = taPref.dumpPath();
				String fileSep = System.getProperty("file.separator");
				dumpFileName += (dumpFileName.endsWith(fileSep) ? "" : fileSep);
				dumpFileName = dumpFileName + "rankingFunctions.smt2";
				// FIXME: add file name
				try {
					script = new LoggingScript(script, dumpFileName, true);
				} catch (FileNotFoundException e) {
					throw new AssertionError(e);
				}
			}
			
			script.setOption(":produce-unsat-cores", true);
			script.setOption(":produce-models", true);
			if (taPref.solver() == Solver.SMTInterpol) {
				script.setLogic(nonlinear ? "QF_NRA" : "QF_LRA");
			} else if (taPref.solver() == Solver.Z3) {
				script.setLogic(nonlinear ? "QF_NRA" : "QF_LRA");
			} else {
				throw new AssertionError();
			}
			return script;
		}
		

		

		

		private void refineBuchi() throws AutomataLibraryException {
			assert m_InterpolAutomaton == null;
			NestedWord<CodeBlock> stem = m_Counterexample.getStem().getWord();
			NestedWord<CodeBlock> loop = m_Counterexample.getLoop().getWord();
			
//			assert m_TraceChecker == null;
//			m_TraceChecker = new TraceChecker(m_SmtManager,
//					m_RootNode.getRootAnnot().getModifiedVars(),
//					m_RootNode.getRootAnnot().getEntryNodes(),
//					null);
			m_TraceChecker = new TraceChecker(m_SmtManager,
					buchiModGlobalVarManager,
					m_RootNode.getRootAnnot().getEntryNodes(),
					null);
			LBool stemCheck = m_TraceChecker.checkTrace(m_Bspm.getStemPrecondition(), m_Bspm.getStemPostcondition(), stem);
			IPredicate[] stemInterpolants;
			if (stemCheck == LBool.UNSAT) {
				stemInterpolants = m_TraceChecker.getInterpolants(new TraceChecker.AllIntegers());
			} else {
				throw new AssertionError();
			}
			m_TraceChecker = new TraceChecker(m_SmtManager,
					buchiModGlobalVarManager,
					m_RootNode.getRootAnnot().getEntryNodes(),
					null);
			LBool loopCheck = m_TraceChecker.checkTrace(m_Bspm.getRankEqAndSi(), m_Bspm.getHondaPredicate(), loop);
			IPredicate[] loopInterpolants;
			if (loopCheck == LBool.UNSAT) {
				loopInterpolants = m_TraceChecker.getInterpolants(new TraceChecker.AllIntegers());
			} else {
				throw new AssertionError();
			}
			
			m_InterpolAutomaton = constructBuchiInterpolantAutomaton(
					m_Bspm.getStemPrecondition(), stem, stemInterpolants, m_Bspm.getHondaPredicate(), 
					loop, loopInterpolants, m_Abstraction);
			if (m_Pref.dumpAutomata()) {
				String filename = "InterpolantAutomatonBuchi"+m_Iteration;
				writeAutomatonToFile(m_InterpolAutomaton, filename);
			}
			EdgeChecker ec = new BuchiEdgeChecker(m_SmtManager, buchiModGlobalVarManager,
					m_Bspm.getHondaPredicate(), m_Bspm.getRankEqAndSi(), 
					m_Bspm.getUnseededVariable(), m_Bspm.getOldRankVariable());
			assert (new InductivityCheck(m_InterpolAutomaton, ec, false, true)).getResult();
			assert (new BuchiAccepts<CodeBlock, IPredicate>(m_InterpolAutomaton,m_Counterexample.getNestedLassoWord())).getResult();
			

			INestedWordAutomatonSimple<CodeBlock, IPredicate> interpolAutomatonUsedInRefinement;
			if (m_Eager) {
				interpolAutomatonUsedInRefinement = new BuchiInterpolantAutomaton(
						m_SmtManager, ec, m_Bspm.getStemPrecondition(), 
						stemInterpolants, m_Bspm.getHondaPredicate(), 
						m_Bspm.getRankEqAndSi(), loopInterpolants, m_Abstraction); 
						//new EagerInterpolantAutomaton(ec, m_InterpolAutomaton);
			} else {
				interpolAutomatonUsedInRefinement = m_InterpolAutomaton;
			}
			IStateDeterminizer<CodeBlock, IPredicate> stateDeterminizer = 
					new PowersetDeterminizer<CodeBlock, IPredicate>(interpolAutomatonUsedInRefinement, m_UseDoubleDeckers);
			INestedWordAutomatonOldApi<CodeBlock, IPredicate> newAbstraction;
			if (m_Difference) {
				BuchiDifferenceFKV<CodeBlock, IPredicate> diff = 
						new BuchiDifferenceFKV<CodeBlock, IPredicate>(
								m_Abstraction, interpolAutomatonUsedInRefinement, 
								stateDeterminizer, m_StateFactoryForRefinement);
				assert diff.checkResult(defaultStateFactory);
				newAbstraction = diff.getResult();
			} else {
				BuchiComplementFKV<CodeBlock, IPredicate> complNwa = 
						new BuchiComplementFKV<CodeBlock, IPredicate>(interpolAutomatonUsedInRefinement, stateDeterminizer);
				assert(complNwa.checkResult(defaultStateFactory));
				INestedWordAutomatonOldApi<CodeBlock, IPredicate>  complement = 
						complNwa.getResult();
				if (interpolAutomatonUsedInRefinement instanceof BuchiInterpolantAutomaton) {
					BuchiInterpolantAutomaton bia = ((BuchiInterpolantAutomaton) interpolAutomatonUsedInRefinement);
					INestedWordAutomatonOldApi<CodeBlock, IPredicate> oldApi = (new RemoveUnreachable<CodeBlock, IPredicate>(bia)).getResult();
					assert (new BuchiAccepts<CodeBlock, IPredicate>(oldApi,m_Counterexample.getNestedLassoWord())).getResult();
				}
				assert !(new BuchiAccepts<CodeBlock, IPredicate>(complement,m_Counterexample.getNestedLassoWord())).getResult();
				BuchiIntersect<CodeBlock, IPredicate> interNwa = 
						new BuchiIntersect<CodeBlock, IPredicate>(m_Abstraction, complement,m_StateFactoryForRefinement);
				assert(interNwa.checkResult(defaultStateFactory));
				newAbstraction = interNwa.getResult();
			}
			if (interpolAutomatonUsedInRefinement instanceof BuchiInterpolantAutomaton) {
				BuchiInterpolantAutomaton bia = ((BuchiInterpolantAutomaton) interpolAutomatonUsedInRefinement);
				bia.clearAssertionStack();
				INestedWordAutomatonOldApi<CodeBlock, IPredicate> oldApi = (new RemoveUnreachable<CodeBlock, IPredicate>(bia)).getResult();
				assert (new BuchiAccepts<CodeBlock, IPredicate>(oldApi,m_Counterexample.getNestedLassoWord())).getResult();
			}
			assert !(new BuchiAccepts<CodeBlock, IPredicate>(newAbstraction,m_Counterexample.getNestedLassoWord())).getResult();
			m_Abstraction = newAbstraction;
		}
		
	
		private NestedWordAutomaton<CodeBlock, IPredicate> constructBuchiInterpolantAutomaton(
				IPredicate precondition, NestedWord<CodeBlock> stem, IPredicate[] stemInterpolants, 
				IPredicate honda, NestedWord<CodeBlock> loop, IPredicate[] loopInterpolants,
				INestedWordAutomatonSimple<CodeBlock, IPredicate> abstraction) {
			NestedWordAutomaton<CodeBlock, IPredicate> result =	
					new NestedWordAutomaton<CodeBlock, IPredicate>(abstraction.getInternalAlphabet(), 
							abstraction.getCallAlphabet(), abstraction.getReturnAlphabet(), 
							abstraction.getStateFactory());
			result.addState(true, false, precondition);
			for (int i=0; i<stemInterpolants.length; i++) {
				addState(stemInterpolants[i], result);
				addTransition(i, precondition, stemInterpolants, honda, stem, result);
			}
			result.addState(false, true, honda);
			addTransition(stemInterpolants.length, precondition, stemInterpolants, honda, stem, result);
			for (int i=0; i<loopInterpolants.length; i++) {
				addState(loopInterpolants[i], result);
				addTransition(i, honda, loopInterpolants, honda, loop, result);
			}
			addTransition(loopInterpolants.length, honda, loopInterpolants, honda, loop, result);
			return result;
		}
		
		private void addState(IPredicate pred, NestedWordAutomaton<CodeBlock, IPredicate> nwa) {
			if (!nwa.getStates().contains(pred)) {
				nwa.addState(false,false,pred);
			}
		}
		
		private void addTransition(int pos, IPredicate pre, IPredicate[] predicates, 
				IPredicate post, NestedWord<CodeBlock> nw, NestedWordAutomaton<CodeBlock, IPredicate> nwa) {
			IPredicate pred = getPredicateAtPosition(pos-1, pre, predicates, post);
			IPredicate succ = getPredicateAtPosition(pos, pre, predicates, post);
			CodeBlock cb = nw.getSymbol(pos);
			if (nw.isInternalPosition(pos)) {
				nwa.addInternalTransition(pred, cb, succ);
			} else if (nw.isCallPosition(pos)) {
				nwa.addCallTransition(pred, cb, succ);
			} else if (nw.isReturnPosition(pos)) {
				assert !nw.isPendingReturn(pos);
				int k = nw.getCallPosition(pos);
				IPredicate hier = getPredicateAtPosition(k-1, pre, predicates, post);
				nwa.addReturnTransition(pred, hier, cb, succ);
			}
		}
		
		private IPredicate getPredicateAtPosition(int pos, IPredicate before, IPredicate[] predicates, IPredicate after) {
			assert pos >= -1;
			assert pos <= predicates.length;
			if (pos < 0) {
				return before;
			} else if (pos >= predicates.length) {
				return after;
			} else {
				return predicates[pos];
			}
		}
		
		public static Collection<Set<IPredicate>> computePartition(INestedWordAutomatonOldApi<CodeBlock, IPredicate> automaton) {
			s_Logger.info("Start computation of initial partition.");
			Collection<IPredicate> states = automaton.getStates();
			Map<ProgramPoint, Set<IPredicate>> accepting = new HashMap<ProgramPoint, Set<IPredicate>>();
			Map<ProgramPoint, Set<IPredicate>> nonAccepting = new HashMap<ProgramPoint, Set<IPredicate>>();
			for (IPredicate p : states) {
				ISLPredicate sp = (ISLPredicate) p;
				if (automaton.isFinal(p)) {
					Set<IPredicate> statesWithSamePP = accepting.get(sp.getProgramPoint());
					if (statesWithSamePP == null) {
						statesWithSamePP = new HashSet<IPredicate>();
						accepting.put(sp.getProgramPoint(), statesWithSamePP);
					}
					statesWithSamePP.add(p);
				} else {
					Set<IPredicate> statesWithSamePP = nonAccepting.get(sp.getProgramPoint());
					if (statesWithSamePP == null) {
						statesWithSamePP = new HashSet<IPredicate>();
						nonAccepting.put(sp.getProgramPoint(), statesWithSamePP);
					}
					statesWithSamePP.add(p);
				}
			}
			Collection<Set<IPredicate>> partition = new ArrayList<Set<IPredicate>>();
			for (ProgramPoint pp : accepting.keySet()) {
				Set<IPredicate> statesWithSamePP = accepting.get(pp);
				partition.add(statesWithSamePP);
			}
			for (ProgramPoint pp : nonAccepting.keySet()) {
				Set<IPredicate> statesWithSamePP = nonAccepting.get(pp);
				partition.add(statesWithSamePP);
			}
			s_Logger.info("Finished computation of initial partition.");
			return partition;
		}
		
		

		
		
		protected void writeAutomatonToFile(
				IAutomaton<CodeBlock, IPredicate> automaton, String filename) {
			new AtsDefinitionPrinter<String,String>(filename, 
					m_Pref.dumpPath()+"/"+filename, Labeling.NUMERATE,"",automaton);
		}
		
}
