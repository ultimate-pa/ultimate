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
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter.Labeling;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DifferenceDD;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceValues.Solver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences.InterpolatedLocs;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CFG2NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.StrongestPostDeterminizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.AnnotateAndAsserter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker.AllIntegers;
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
		
		private final BinaryStatePredicateManager m_Binarizer;
		
		protected IAutomaton<CodeBlock, IPredicate> m_ArtifactAutomaton;
		
		// used for the collection of statistics
		public int m_BiggestAbstractionIteration = 0;
		public int m_BiggestAbstractionSize = 0;
		public int m_InitialAbstractionSize = 0;

		private NestedRun<CodeBlock, IPredicate> m_ConcatenatedCounterexample;

		private IPredicate m_TruePredicate;

		private IPredicate m_FalsePredicate;
		
		public BuchiCegarLoop(RootNode rootNode,
				SmtManager smtManager,
				TAPreferences taPrefs,
				Collection<ProgramPoint> errorLocs) {
			this.m_Name = "BuchiCegarLoop";
			this.m_RootNode = rootNode;
			this.m_SmtManager = smtManager;
			this.m_Binarizer = new BinaryStatePredicateManager(smtManager);
			this.m_Pref = taPrefs;
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
			
			
			
//			for (m_Iteration=1; m_Iteration<=m_Pref.maxIterations(); m_Iteration++){
//				s_Logger.info("======== Iteration " + m_Iteration + "============");
//				m_SmtManager.setIteration(m_Iteration);
//
//				
//				
//				LBool isCounterexampleFeasible = isCounterexampleFeasible();
//				if (isCounterexampleFeasible == Script.LBool.SAT) {
//					return Result.UNSAFE;
//				}
//				if (isCounterexampleFeasible == Script.LBool.UNKNOWN) {
//					return Result.UNKNOWN;
//				}
//				
//
//				
//				
//				constructInterpolantAutomaton();
//				
//				s_Logger.info("Interpolant Automaton has "+m_InterpolAutomaton.getStates().size() +" states");
//				
//				if (m_Iteration <= m_Pref.watchIteration() && m_Pref.artifact() == Artifact.INTERPOLANT_AUTOMATON) {
//					m_ArtifactAutomaton = m_InterpolAutomaton;
//				}
//				if (m_Pref.dumpAutomata()) {
//					writeAutomatonToFile(m_InterpolAutomaton, "InterpolantAutomaton_Iteration"+m_Iteration);
//				}
//				
//				
//				
//				
//				try {
//					boolean progress = refineAbstraction();
//					if (!progress) {
//						s_Logger.warn("No progress! Counterexample is still accepted by refined abstraction.");
//						assert (m_Pref.interpolatedLocs() == InterpolatedLocs.GUESS) :
//								"Craig interpolation && no progress   ==>   bug!";
//						m_FailurePath = AnnotateAndAsserter.constructFailureTrace(m_Counterexample.getWord(), null);
//						return Result.UNKNOWN;
//					}
//				} catch (OperationCanceledException e) {
//					s_Logger.warn("Verification cancelled");
//					return Result.TIMEOUT;
//				} catch (AutomataLibraryException e) {
//					throw new AssertionError("Automata Operation failed" + e.getMessage());
//				}
//				
//				s_Logger.info("Abstraction has " + m_Abstraction.sizeInformation());
//				s_Logger.info("Interpolant automaton has " + m_InterpolAutomaton.sizeInformation());
//				
//
//				if (m_Pref.computeHoareAnnotation()) {
//					assert (m_SmtManager.checkInductivity(m_Abstraction, false, true));
//				}
//
//				if (m_Iteration <= m_Pref.watchIteration() && m_Pref.artifact() == Artifact.ABSTRACTION) {
//					m_ArtifactAutomaton = m_Abstraction;
//				}
//				
//				if (m_Pref.dumpAutomata()) {
//					String filename = "Abstraction"+m_Iteration;
//					writeAutomatonToFile(m_Abstraction, filename);
//				}
//				
//				if (m_BiggestAbstractionSize < m_Abstraction.size()){
//					m_BiggestAbstractionSize = m_Abstraction.size();
//					m_BiggestAbstractionIteration = m_Iteration;
//				}
//				
//				
//				
//				
//				
//				boolean isAbstractionCorrect;
//				try {
//					isAbstractionCorrect = isAbstractionCorrect();
//				} catch (OperationCanceledException e) {
//					s_Logger.warn("Verification cancelled");
//					return Result.TIMEOUT;
//				}
//				if (isAbstractionCorrect) {
//					return Result.SAFE;
//				}
//			}
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
				PredicateFactory defaultStateFactory = new PredicateFactory(
						m_SmtManager,
						m_Pref);
			Collection<ProgramPoint> allpp = new HashSet<ProgramPoint>();
			for (Map<String, ProgramPoint> test : m_RootNode.getRootAnnot().getProgramPoints().values()) {
				allpp.addAll(test.values());
			}
			m_Abstraction = cFG2NestedWordAutomaton.getNestedWordAutomaton(
					m_RootNode, defaultStateFactory, allpp);
		}
		
		
		private LBool isCounterexampleFeasible() {
			assert m_ConcatenatedCounterexample == null;
			NestedRun<CodeBlock, IPredicate> stem = m_Counterexample.getStem();
			s_Logger.info("Stem: " + stem);
			NestedRun<CodeBlock, IPredicate> loop = m_Counterexample.getLoop();
			s_Logger.info("Loop: " + loop);
			m_ConcatenatedCounterexample = stem.concatenate(loop);

			m_TraceChecker = new TraceChecker(m_SmtManager,
					m_RootNode.getRootAnnot().getModifiedVars(),
					m_RootNode.getRootAnnot().getEntryNodes(),
					null);
			m_TruePredicate = m_SmtManager.newTruePredicate();
			m_FalsePredicate = m_SmtManager.newFalsePredicate();

			LBool feasibility = m_TraceChecker.checkTrace(
					m_TruePredicate, m_FalsePredicate, m_ConcatenatedCounterexample.getWord());
			return feasibility;
		}
		
		private void refineFinite() throws OperationCanceledException {
			AllIntegers allInt = new TraceChecker.AllIntegers();
			IPredicate[] interpolants = m_TraceChecker.getInterpolants(allInt);
			constructInterpolantAutomaton(interpolants);
			StrongestPostDeterminizer spd = new StrongestPostDeterminizer(
					m_SmtManager, m_Pref, m_InterpolAutomaton);
			DifferenceDD<CodeBlock, IPredicate> diff = null;
			try {
				diff = new DifferenceDD<CodeBlock, IPredicate>(
						m_Abstraction, m_InterpolAutomaton, spd, 
						m_Abstraction.getStateFactory(),
						false, true);
			} catch (AutomataLibraryException e) {
				if (e instanceof OperationCanceledException) {
					throw (OperationCanceledException) e;
				} else {
					throw new AssertionError();
				}
			}
			m_Abstraction = diff.getResult();
			m_ConcatenatedCounterexample = null;
			m_TraceChecker = null;

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
		
		
		
		boolean isCounterexampleTerminating() {
			CodeBlock[] stemCBs = new CodeBlock[m_Counterexample.getStem().getLength()];
			for (int i=0; i<m_Counterexample.getStem().getLength(); i++) {
				stemCBs[i] = m_Counterexample.getStem().getSymbol(i);
			}
			CodeBlock[] loopCBs = new CodeBlock[m_Counterexample.getLoop().getLength()];
			for (int i=0; i<m_Counterexample.getLoop().getLength(); i++) {
				loopCBs[i] = m_Counterexample.getLoop().getSymbol(i);
			}
			@SuppressWarnings("deprecation")
			TransFormula stemTF = SequentialComposition.getInterproceduralTransFormula(
					m_RootNode.getRootAnnot().getBoogie2SMT(), m_RootNode.getRootAnnot().getTaPrefs().SimplifyCodeBlocks(), false, stemCBs);
			int stemVars = stemTF.getFormula().getFreeVars().length;

			@SuppressWarnings("deprecation")
			TransFormula loopTF = SequentialComposition.getInterproceduralTransFormula(
					m_RootNode.getRootAnnot().getBoogie2SMT(), m_RootNode.getRootAnnot().getTaPrefs().SimplifyCodeBlocks(),false, loopCBs);
			int loopVars = loopTF.getFormula().getFreeVars().length;
			s_Logger.info("Statistics: stemVars: " + stemVars + "loopVars: " + loopVars);
			{
				List<CodeBlock> composedCB = new ArrayList<CodeBlock>();
				composedCB.addAll(Arrays.asList(stemCBs));
				composedCB.addAll(Arrays.asList(loopCBs));
//				composedCB.addAll(Arrays.asList(loopCBs));
				TransFormula composed = SequentialComposition.getInterproceduralTransFormula(
						m_RootNode.getRootAnnot().getBoogie2SMT(), false, m_RootNode.getRootAnnot().getTaPrefs().SimplifyCodeBlocks(), composedCB.toArray(new CodeBlock[0])); 
						//TransFormula.sequentialComposition(10000, rootAnnot.getBoogie2SMT(), stemTF, loopTF);
				if (composed.isInfeasible() == Infeasibility.INFEASIBLE) {
					throw new AssertionError("suddently infeasible");
				}
			}
			NestedWord<CodeBlock> emptyWord = new NestedWord<CodeBlock>();
			boolean withoutStem = synthesize(emptyWord, m_Counterexample.getLoop().getWord(), getDummyTF(), loopTF);
			boolean witStem = synthesize(m_Counterexample.getStem().getWord(), m_Counterexample.getLoop().getWord(), stemTF, loopTF);
			if (witStem && !withoutStem) {
				s_Logger.info("Statistics: SI IS NECESSARY !!!");
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
					Collection<SupportingInvariant> si_list = synthesizer
							.getSupportingInvariants();
					assert (si_list != null);

					StringBuilder longMessage = new StringBuilder();
					LinearRankingFunction linRf = (LinearRankingFunction) rf;
					Expression rfExp = linRf.asExpression(m_SmtManager.getScript(),
							m_SmtManager.getBoogieVar2SmtVar());
					String rfString = RankingFunctionsObserver
							.backtranslateExprWorkaround(rfExp);
					String siString;

					// if (si_list.size() <= 2) {
					// SupportingInvariant si = si_list.iterator().next();
					// Expression siExp = si.asExpression(smtManager.getScript(),
					// rootAnnot.getBoogie2Smt());
					// siString =
					// RankingFunctionsObserver.backtranslateExprWorkaround(siExp);
					// } else {
					// throw new
					// AssertionError("The linear template should not have more than two supporting invariants.");
					// }
					longMessage.append("Statistics: Found linear ranking function ");
					longMessage.append(rfString);
					longMessage.append(" with linear supporting invariant");
					for (SupportingInvariant si : si_list) {
						Expression siExp = si.asExpression(m_SmtManager.getScript(),
								m_SmtManager.getBoogieVar2SmtVar());
						siString = RankingFunctionsObserver
								.backtranslateExprWorkaround(siExp);
						longMessage.append(" " + siString);
					}
					longMessage.append("  length stem: " + stem.length()
							+ " length loop: " + loop.length());
					s_Logger.info(longMessage);

					for (SupportingInvariant si : si_list) {
						if (stem.length() > 0) {
							assert checkResult(si, stem, loop) : "Wrong supporting invariant "
								+ si;
						}
					}
					boolean correctWithoutSi = checkResult(linRf, loop);
					if (correctWithoutSi) {
						s_Logger.info("Statistics: For this ranking function no si needed");
					} else {
						s_Logger.info("Statistics: We need si for this ranking function");
					}
					assert checkResult(linRf, si_list, loop) : "Wrong ranking function "
							+ rf;

				} else {
					s_Logger.info("Statistics: No ranking function has been found "
							+ "with this template.");
				}
			} catch (SMTLIBException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (TermIsNotAffineException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (InstantiationException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (AssertionError e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
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
		
		private static boolean isTrue(IPredicate pred) {
			Term term = pred.getFormula();
			if (term instanceof ApplicationTerm) {
				ApplicationTerm appTerm = (ApplicationTerm) term;
				if (appTerm.getFunction().getName().equals("true")) {
					return true;
				}
			}
			return false;
		}
		
		private boolean checkResult(SupportingInvariant si, NestedWord<CodeBlock> stem, NestedWord<CodeBlock> loop) {
			boolean result = true;
			m_TraceChecker = new TraceChecker(m_SmtManager,
					m_RootNode.getRootAnnot().getModifiedVars(),
					m_RootNode.getRootAnnot().getEntryNodes(),
					null);
			IPredicate siPred = m_Binarizer.supportingInvariant2Predicate(si);
			if (isTrue(siPred)) {
				siPred = m_TruePredicate;
			}
			LBool stemCheck = m_TraceChecker.checkTrace(m_TruePredicate, siPred, stem);
			if (stemCheck == LBool.UNSAT) {
				IPredicate[] interpolants = m_TraceChecker.getInterpolants(new TraceChecker.AllIntegers());
				interpolants.toString();
			} else {
				result = false;			
			}
			LBool loopCheck = m_TraceChecker.checkTrace(siPred, siPred, stem);
			if (loopCheck == LBool.UNSAT) {
				IPredicate[] interpolants = m_TraceChecker.getInterpolants(new TraceChecker.AllIntegers());
				interpolants.toString();
			} else {
				result = false;
			}
			return result;
		}
		
		private boolean checkResult(RankingFunction rf, NestedWord<CodeBlock> loop) {
			boolean result = true;
			IPredicate seedEquality = m_Binarizer.getSeedVarEquality(rf);
			IPredicate rkDecrease = m_Binarizer.getRankDecrease(rf);
			
			LBool stemCheck = m_TraceChecker.checkTrace(seedEquality, rkDecrease, loop);
			m_TraceChecker.forgetTrace();
			if (stemCheck != LBool.UNSAT) {
				result = false;
			}
			return result;
		}

		
		private boolean checkResult(RankingFunction rf,  Iterable<SupportingInvariant> siList, NestedWord<CodeBlock> loop) {
			boolean result = true;
			List<IPredicate> siPreds = new ArrayList<IPredicate>();
			for (SupportingInvariant si : siList) {
				IPredicate siPred = m_Binarizer.supportingInvariant2Predicate(si);
				siPreds.add(siPred);
			}
			TermVarsProc tvp = m_SmtManager.and(siPreds.toArray(new IPredicate[0]));
			IPredicate siConjunction = m_SmtManager.newPredicate(tvp.getFormula(), 
					tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula()); 
			
			IPredicate seedEquality = m_Binarizer.getSeedVarEquality(rf);
			IPredicate rkDecrease = m_Binarizer.getRankDecrease(rf);
			
			final IPredicate siConjunctionAndSeedEquality;
			{
				tvp = m_SmtManager.and(siConjunction, seedEquality);
				siConjunctionAndSeedEquality = m_SmtManager.newPredicate(tvp.getFormula(), 
						tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
			}
			
			LBool stemCheck = m_TraceChecker.checkTrace(siConjunctionAndSeedEquality, rkDecrease, loop);
			m_TraceChecker.forgetTrace();
			if (stemCheck != LBool.UNSAT) {
				result = false;
			}
			return result;
		}
		
		
		
		
		protected void writeAutomatonToFile(
				IAutomaton<CodeBlock, IPredicate> automaton, String filename) {
			new AtsDefinitionPrinter<String,String>(filename, 
					m_Pref.dumpPath()+"/"+filename, Labeling.TOSTRING,"",automaton);
		}
		
}
