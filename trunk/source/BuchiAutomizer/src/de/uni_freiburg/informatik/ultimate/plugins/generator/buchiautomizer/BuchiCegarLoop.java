package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;

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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DifferenceDD;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.AnnotateAndAsserter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker.AllIntegers;

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
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			try {
				m_Abstraction = (NestedWordAutomaton<CodeBlock, IPredicate>) diff.getResult();
			} catch (OperationCanceledException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
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
		
		
		
		
		
		protected void writeAutomatonToFile(
				IAutomaton<CodeBlock, IPredicate> automaton, String filename) {
			new AtsDefinitionPrinter<String,String>(filename, 
					m_Pref.dumpPath()+"/"+filename, Labeling.TOSTRING,"",automaton);
		}
		
}
