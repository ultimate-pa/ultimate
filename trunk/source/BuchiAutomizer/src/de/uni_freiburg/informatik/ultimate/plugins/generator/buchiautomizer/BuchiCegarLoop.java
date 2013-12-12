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
import java.util.TreeMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter.Labeling;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiClosureNwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveNonLiveStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DifferenceDD;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.structure.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.RefineBuchi.RefinementSetting;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.PreferenceInitializer.BInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.RankingFunctionsObserver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.RankingFunctionsSynthesizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.SupportingInvariant;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.TermIsNotAffineException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.functions.LinearRankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.functions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.templates.LinearTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula.Infeasibility;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker.AllIntegers;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerSpWp;
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
		
		private static final String LTL_MODE_IDENTIFIER = "BuchiProgramProrduct";
		
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

		private PredicateFactory m_DefaultStateFactory;

		private HoareAnnotationFragments m_Haf;

		private PredicateFactoryRefinement m_StateFactoryForRefinement;

		private BuchiModGlobalVarManager buchiModGlobalVarManager;
		
		private final TreeMap<Integer,Integer> m_ModuleSizeTrivial = new TreeMap<Integer,Integer>();
		private final TreeMap<Integer,Integer> m_ModuleSizeDeterministic = new TreeMap<Integer,Integer>();
		private final TreeMap<Integer,Integer> m_ModuleSizeNondeterministic = new TreeMap<Integer,Integer>();
		private final TreeMap<Integer,Expression> m_RankingFunction = new TreeMap<Integer,Expression>();

		
		private static final boolean m_ExternalSolver = false;
		private static final boolean m_SimplifyStemAndLoop = true;
		private static final boolean m_ReduceAbstractionSize = true;
		
		
		private final boolean m_Difference;
		private final boolean m_UseDoubleDeckers;
		private final BInterpolantAutomaton m_InterpolantAutomaton;
		private final boolean m_BouncerStem;
		private final boolean m_BouncerLoop;
		private final boolean m_ScroogeNondeterminismStem;
		private final boolean m_ScroogeNondeterminismLoop;
		private final boolean m_CannibalizeLoop;
		private final int m_MaxNumberOfLoopUnwindings;
		
		private final RefineBuchi m_RefineBuchi;
		private final List<RefineBuchi.RefinementSetting> m_BuchiRefinementSettingSequence;


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
			m_DefaultStateFactory = new PredicateFactory(
					m_SmtManager,
					m_Pref);
			
			m_Haf = new HoareAnnotationFragments(rootNode.getRootAnnot(),m_SmtManager);
			m_StateFactoryForRefinement = new PredicateFactoryRefinement(
					m_RootNode.getRootAnnot().getProgramPoints(),
					m_SmtManager,
					m_Pref,
					false && m_Pref.computeHoareAnnotation(),
					m_Haf);
			
			UltimatePreferenceStore baPref = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
			
			m_UseDoubleDeckers = !baPref.getBoolean(PreferenceInitializer.LABEL_IgnoreDownStates);
			m_Difference = baPref.getBoolean(PreferenceInitializer.LABEL_DeterminizationOnDemand);
			m_InterpolantAutomaton = baPref.getEnum(PreferenceInitializer.LABEL_BuchiInterpolantAutomaton, BInterpolantAutomaton.class);
			m_BouncerStem = baPref.getBoolean(PreferenceInitializer.LABEL_BouncerStem);
			m_BouncerLoop = baPref.getBoolean(PreferenceInitializer.LABEL_BouncerLoop);
			m_ScroogeNondeterminismStem = baPref.getBoolean(PreferenceInitializer.LABEL_ScroogeNondeterminismStem);
			m_ScroogeNondeterminismLoop = baPref.getBoolean(PreferenceInitializer.LABEL_ScroogeNondeterminismLoop);
			if ((m_ScroogeNondeterminismStem || m_ScroogeNondeterminismLoop) && m_InterpolantAutomaton != BInterpolantAutomaton.ScroogeNondeterminism) {
				throw new IllegalArgumentException("illegal combination of settings");
			}
			if ((!m_ScroogeNondeterminismStem && !m_ScroogeNondeterminismLoop) && m_InterpolantAutomaton == BInterpolantAutomaton.ScroogeNondeterminism) {
				throw new IllegalArgumentException("illegal combination of settings");
			}
			m_CannibalizeLoop = baPref.getBoolean(PreferenceInitializer.LABEL_CannibalizeLoop);
			m_MaxNumberOfLoopUnwindings = baPref.getInt(PreferenceInitializer.LABEL_LoopUnwindings);
			
			m_RefineBuchi = new RefineBuchi(m_SmtManager, m_Bspm, 
					buchiModGlobalVarManager, m_Pref.dumpAutomata(), 
					m_Difference, m_DefaultStateFactory, m_StateFactoryForRefinement, m_UseDoubleDeckers, 
					m_Pref.dumpPath(), m_Pref.interpolation());
			m_BuchiRefinementSettingSequence = new ArrayList<RefineBuchi.RefinementSetting>();
			switch (m_InterpolantAutomaton) {
			case Staged:
				m_BuchiRefinementSettingSequence.add( 
						m_RefineBuchi.new RefinementSetting(BInterpolantAutomaton.Deterministic, true, false, false, false, true));
				m_BuchiRefinementSettingSequence.add( 
						m_RefineBuchi.new RefinementSetting(BInterpolantAutomaton.Deterministic, true, true, false, false, true));
				m_BuchiRefinementSettingSequence.add( 
						m_RefineBuchi.new RefinementSetting(BInterpolantAutomaton.ScroogeNondeterminism, true, false, true, false, false));
				m_BuchiRefinementSettingSequence.add( 
						m_RefineBuchi.new RefinementSetting(BInterpolantAutomaton.ScroogeNondeterminism, true, true, true, false, false));
				m_BuchiRefinementSettingSequence.add( 
						m_RefineBuchi.new RefinementSetting(BInterpolantAutomaton.ScroogeNondeterminism, false, false, true, true, false));
				break;
			case LassoAutomaton:
			case EagerNondeterminism:
			case ScroogeNondeterminism:
			case Deterministic:
				m_BuchiRefinementSettingSequence.add( 
						m_RefineBuchi.new RefinementSetting(m_InterpolantAutomaton, m_BouncerStem, m_BouncerLoop, m_ScroogeNondeterminismStem, m_ScroogeNondeterminismLoop, m_CannibalizeLoop));
				break;
			default:
				throw new UnsupportedOperationException("unknown automaton");
			}
		}
		
		NestedLassoRun<CodeBlock, IPredicate> getCounterexample() {
			return m_Counterexample;
		}
		
		static boolean emptyStem(NestedLassoRun<CodeBlock, IPredicate> nlr) {
			assert nlr.getStem().getLength() > 0;
			return nlr.getStem().getLength() == 1;
		}
		
		
		
		public final Result iterate() {
			s_Logger.info("Interprodecural is " + m_Pref.interprocedural());		
			s_Logger.info("Hoare is " + m_Pref.computeHoareAnnotation());
			s_Logger.info("Compute interpolants for " + m_Pref.interpolation());
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
				writeAutomatonToFile(m_Abstraction, m_Pref.dumpPath(), filename);
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
						m_TraceChecker.unlockSmtManager();
						boolean terminating = isCounterexampleTerminating(
								m_Counterexample.getStem().getWord(), m_Counterexample.getLoop().getWord());
						if (!terminating) {
							return Result.UNKNOWN;
						} else {
							m_ConcatenatedCounterexample = null;

							INestedWordAutomatonOldApi<CodeBlock, IPredicate> newAbstraction = refineBuchi();
							m_Abstraction = newAbstraction;
						}
					} else {
						throw new AssertionError();
					}

					s_Logger.info("Abstraction has " + m_Abstraction.sizeInformation());
//					s_Logger.info("Interpolant automaton has " + m_RefineBuchi.getInterpolAutomatonUsedInRefinement().sizeInformation());
					
					if (m_ReduceAbstractionSize ) {
						m_Abstraction = (new RemoveNonLiveStates<CodeBlock, IPredicate>(m_Abstraction)).getResult();
						m_Abstraction = (INestedWordAutomatonOldApi<CodeBlock, IPredicate>) (new BuchiClosureNwa(m_Abstraction));
						m_Abstraction = (new RemoveDeadEnds<CodeBlock, IPredicate>(m_Abstraction)).getResult();
						s_Logger.info("Abstraction has " + m_Abstraction.sizeInformation());
						Collection<Set<IPredicate>> partition = BuchiCegarLoop.computePartition(m_Abstraction);
						MinimizeSevpa<CodeBlock, IPredicate> minimizeOp = 
								new MinimizeSevpa<CodeBlock, IPredicate>(m_Abstraction, partition, false, false, m_StateFactoryForRefinement);
						assert (minimizeOp.checkResult(m_DefaultStateFactory));
						INestedWordAutomatonOldApi<CodeBlock, IPredicate> minimized = minimizeOp.getResult();
						if (m_Pref.computeHoareAnnotation()) {
							Map<IPredicate, IPredicate> oldState2newState = minimizeOp.getOldState2newState();
							throw new AssertionError("not supported");
						}
						m_Abstraction = minimized;
						s_Logger.info("Abstraction has " + m_Abstraction.sizeInformation());
					}


//					if (m_Pref.computeHoareAnnotation()) {
//						assert (m_SmtManager.checkInductivity(m_Abstraction, false, true));
//					}

					if (m_Iteration <= m_Pref.watchIteration() && m_Pref.artifact() == Artifact.ABSTRACTION) {
						m_ArtifactAutomaton = m_Abstraction;
					}

					if (m_Pref.dumpAutomata()) {
						String filename = "Abstraction"+m_Iteration;
						writeAutomatonToFile(m_Abstraction, m_Pref.dumpPath(), filename);
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
		
		INestedWordAutomatonOldApi<CodeBlock, IPredicate> refineBuchi() throws AutomataLibraryException {
			int stage = 0;
			for (RefinementSetting rs  : m_BuchiRefinementSettingSequence) {
				if (stage > 0) {
					s_Logger.info("Statistics: We needed stage " + stage);
				}
				INestedWordAutomatonOldApi<CodeBlock, IPredicate> newAbstraction = 
						m_RefineBuchi.refineBuchi(m_Abstraction,m_Counterexample, m_Iteration, rs);
				if (newAbstraction != null) {
					switch (rs.getInterpolantAutomaton()) {
					case Deterministic:
					case LassoAutomaton:
						m_ModuleSizeDeterministic.put(m_Iteration,m_RefineBuchi.getInterpolAutomatonUsedInRefinement().size());
						break;
					case ScroogeNondeterminism:
					case EagerNondeterminism:
						m_ModuleSizeNondeterministic.put(m_Iteration,m_RefineBuchi.getInterpolAutomatonUsedInRefinement().size());
						break;
					default:
						throw new AssertionError("unsupported");
					}
					return newAbstraction;
				}
				stage++;
			}
			throw new AssertionError("no settings was sufficient");
			
		}


		private boolean isAbstractionCorrect() throws OperationCanceledException {
			BuchiIsEmpty<CodeBlock, IPredicate> ec = new BuchiIsEmpty<CodeBlock, IPredicate>(m_Abstraction);
			if (ec.getResult()) {
				return true;
			} else {
				m_Counterexample = ec.getAcceptingNestedLassoRun();
				assert m_Counterexample.getLoop().getLength() > 1;
				return false;
			}
		}


		private void getInitialAbstraction() {
			CFG2NestedWordAutomaton cFG2NestedWordAutomaton = 
					new CFG2NestedWordAutomaton(m_Pref,m_SmtManager);
			Collection<ProgramPoint> acceptingNodes;
			Collection<ProgramPoint> allNodes = new HashSet<ProgramPoint>();
			for (Map<String, ProgramPoint> test : m_RootNode.getRootAnnot().getProgramPoints().values()) {
				allNodes.addAll(test.values());
			}
			if (hasLtlAnnotation(m_RootNode)) {
				acceptingNodes = new HashSet<ProgramPoint>();
				for (ProgramPoint pp : allNodes) {
					if (hasLtlAnnotation(pp)) {
						acceptingNodes.add(pp);
					}
				}
			} else {
				acceptingNodes = allNodes;
			}
			m_Abstraction = cFG2NestedWordAutomaton.getNestedWordAutomaton(
					m_RootNode, m_DefaultStateFactory, acceptingNodes);
		}
		
		
		private boolean hasLtlAnnotation(BasePayloadContainer bpc) {
			if (bpc.getPayload().hasAnnotation()) {
				return bpc.getPayload().getAnnotations().containsKey(LTL_MODE_IDENTIFIER);
			} else {
				return false;
			}
		}
		
		
		private LBool isCounterexampleFeasible() {
			assert m_ConcatenatedCounterexample == null;
			assert m_TraceChecker == null;
			NestedRun<CodeBlock, IPredicate> stem = m_Counterexample.getStem();
			s_Logger.info("Stem: " + stem);
			NestedRun<CodeBlock, IPredicate> loop = m_Counterexample.getLoop();
			s_Logger.info("Loop: " + loop);

			m_TruePredicate = m_SmtManager.newTruePredicate();
			m_FalsePredicate = m_SmtManager.newFalsePredicate();
			
			LBool feasibility;
			m_ConcatenatedCounterexample = stem;
			if (emptyStem(m_Counterexample)) {
				feasibility = LBool.SAT;
			} else {
				m_TraceChecker = constructTraceChecker(m_TruePredicate, 
					m_FalsePredicate, null, m_ConcatenatedCounterexample.getWord(), 
					m_SmtManager, m_RootNode.getRootAnnot().getModGlobVarManager());
				feasibility = m_TraceChecker.isCorrect();
				if (feasibility != LBool.UNSAT) {
					m_TraceChecker.unlockSmtManager();
				}
			}
			if (feasibility == LBool.UNSAT) {
				s_Logger.info("stem already infeasible");
			} else {
				m_ConcatenatedCounterexample = loop;
				m_TraceChecker = constructTraceChecker(m_TruePredicate, 
						m_FalsePredicate, null, m_ConcatenatedCounterexample.getWord(),
						m_SmtManager, m_RootNode.getRootAnnot().getModGlobVarManager());
				feasibility = m_TraceChecker.isCorrect();
				if (feasibility == LBool.UNSAT) {
					s_Logger.info("loop already infeasible");
				} else {
					m_TraceChecker.unlockSmtManager();
					m_ConcatenatedCounterexample = stem.concatenate(loop);
					m_TraceChecker = constructTraceChecker(m_TruePredicate, 
							m_FalsePredicate, null, m_ConcatenatedCounterexample.getWord(), 
							m_SmtManager, m_RootNode.getRootAnnot().getModGlobVarManager());
					feasibility = m_TraceChecker.isCorrect();

				}
			}
			return feasibility;
		}
		
		private void refineFinite() throws OperationCanceledException {
			AllIntegers allInt = new TraceChecker.AllIntegers();
			PredicateUnifier pu = new PredicateUnifier(m_SmtManager, 
					m_TruePredicate, m_FalsePredicate);
			m_TraceChecker.computeInterpolants(allInt, pu, m_Pref.interpolation());
			constructInterpolantAutomaton(m_TraceChecker);
			EdgeChecker ec = new EdgeChecker(m_SmtManager, buchiModGlobalVarManager);
			PostDeterminizer spd = new PostDeterminizer(
					ec, m_Pref, m_InterpolAutomaton, true);
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
			if (m_Pref.dumpAutomata()) {
				String filename = "interpolAutomatonUsedInRefinement"+m_Iteration+"after";
				writeAutomatonToFile(m_InterpolAutomaton, m_Pref.dumpPath(), filename);
			}
			m_ModuleSizeTrivial.put(m_Iteration,m_InterpolAutomaton.size());
			assert (new InductivityCheck(m_InterpolAutomaton, ec, false, true)).getResult();
			m_Abstraction = diff.getResult();
			m_ConcatenatedCounterexample = null;
		}
		
		protected void constructInterpolantAutomaton(TraceChecker traceChecker) throws OperationCanceledException {
			InterpolantAutomataBuilder iab = new InterpolantAutomataBuilder(
							m_ConcatenatedCounterexample,
							traceChecker,
							m_Pref.interpolantAutomaton(), m_Pref.edges2True(),
							m_SmtManager, m_Pref,
							m_Iteration, null);
			m_InterpolAutomaton = iab.buildInterpolantAutomaton(
					m_Abstraction, m_Abstraction.getStateFactory());
			
			assert((new Accepts<CodeBlock, IPredicate>(m_InterpolAutomaton, m_ConcatenatedCounterexample.getWord())).getResult()) :
				"Interpolant automaton broken!";
//			assert((new BuchiAccepts<CodeBlock, IPredicate>(m_InterpolAutomaton, m_Counterexample.getNestedLassoWord())).getResult()) :
//				"Interpolant automaton broken!";
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
					m_SimplifyStemAndLoop, true, false, stemCBs);
			int stemVars = stemTF.getFormula().getFreeVars().length;

			@SuppressWarnings("deprecation")
			TransFormula loopTF = SequentialComposition.getInterproceduralTransFormula(
					m_RootNode.getRootAnnot().getBoogie2SMT(),
					m_RootNode.getRootAnnot().getModGlobVarManager(),
					m_SimplifyStemAndLoop, true,false, loopCBs);
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
						m_SimplifyStemAndLoop, true, true, composedCB.toArray(new CodeBlock[0])); 
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
				m_RankingFunction.put(m_Iteration,m_LinRf.asExpression(m_SmtManager.getScript(), m_SmtManager.getSmt2Boogie()));
				return true;
			}
			boolean witStem = synthesize(stem, loop, stemTF, loopTF);
			if (witStem) {
				reportRankingFunction(m_LinRf, honda, stem, loop);
				m_RankingFunction.put(m_Iteration,m_LinRf.asExpression(m_SmtManager.getScript(), m_SmtManager.getSmt2Boogie()));
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
					m_SmtManager.getSmt2Boogie());
			String rfString = RankingFunctionsObserver
					.backtranslateExprWorkaround(rfExp);
			StringBuilder longDescr = new StringBuilder();
			longDescr.append("Derived linear ranking function ");
			longDescr.append(rfString);
			longDescr.append(System.getProperty("line.separator"));
			longDescr.append(" with linear supporting invariants");
			for (SupportingInvariant si : m_SiList) {
				Expression siExp = si.asExpression(m_SmtManager.getScript(),
						m_SmtManager.getSmt2Boogie());
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
			
			if (m_ExternalSolver) {
				script = new Scriptor("z3 -smt2 -in", solverLogger);
			} else {
				script = new SMTInterpol(solverLogger,false);
			}
			
			if (false) {
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
			script.setLogic(nonlinear ? "QF_NRA" : "QF_LRA");
			return script;
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
		
		

		
		
		protected static void writeAutomatonToFile(
				IAutomaton<CodeBlock, IPredicate> automaton, String path, String filename) {
			new AtsDefinitionPrinter<String,String>(filename, 
					path+"/"+filename, Labeling.TOSTRING,"",automaton);
		}


		
		
		public TreeMap<Integer, Integer> getModuleSizeTrivial() {
			return m_ModuleSizeTrivial;
		}

		public TreeMap<Integer, Integer> getModuleSizeDeterministic() {
			return m_ModuleSizeDeterministic;
		}

		public TreeMap<Integer, Integer> getModuleSizeNondeterministic() {
			return m_ModuleSizeNondeterministic;
		}

		public TreeMap<Integer, Expression> getRankingFunction() {
			return m_RankingFunction;
		}
		
		private TraceChecker constructTraceChecker(IPredicate precond,
				IPredicate postcond, Object object,
				NestedWord<CodeBlock> word, SmtManager smtManager,
				ModifiableGlobalVariableManager modGlobalVarManager) {
			switch (m_Pref.interpolation()) {
			case Craig_NestedInterpolation:
			case Craig_TreeInterpolation:
				return new TraceChecker(precond, postcond, 
						null, NestedWord.nestedWord(word),m_SmtManager,
						modGlobalVarManager);
			case ForwardPredicates:
			case BackwardPredicates:
			case FPandSP:
				return new TraceCheckerSpWp(precond, postcond, 
						NestedWord.nestedWord(word),m_SmtManager,
						modGlobalVarManager);
			default:
				throw new UnsupportedOperationException("unsupported interpolation");
			}
		}

		
}
