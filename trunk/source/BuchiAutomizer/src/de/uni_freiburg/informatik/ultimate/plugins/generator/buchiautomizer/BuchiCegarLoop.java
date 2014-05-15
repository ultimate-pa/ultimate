package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.io.File;
import java.util.ArrayList;
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
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.structure.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.NonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.SupportingInvariant;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.TerminationArgument;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.LassoChecker.ContinueDirective;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.RefineBuchi.RefinementSetting;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.PreferenceInitializer.BInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CFG2NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopBenchmarkType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.HoareAnnotationFragments;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryResultChecking;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender.PostDeterminizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.result.TerminationArgumentResult;

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
		public enum Result { TERMINATING, TIMEOUT , UNKNOWN, NONTERMINATING }
		
		
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
		
		protected final BinaryStatePredicateManager m_BinaryStatePredicateManager;
		
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
		 * Interpolant automaton of this iteration.
		 */
		protected NestedWordAutomaton<CodeBlock, IPredicate> m_InterpolAutomaton;
		
		protected IAutomaton<CodeBlock, IPredicate> m_ArtifactAutomaton;
		
		private static final String LTL_MODE_IDENTIFIER = "BuchiProgramProduct";
		
		// used for the collection of statistics
		int m_Infeasible = 0;
		int m_RankWithoutSi = 0;
		int m_RankWithSi = 0;


		
		private final PredicateFactory m_DefaultStateFactory;
		private final PredicateFactoryResultChecking m_PredicateFactoryResultChecking;

		private final HoareAnnotationFragments m_Haf;

		private final PredicateFactoryRefinement m_StateFactoryForRefinement;

		private final ModuleDecompositionBenchmark m_MDBenchmark = 
				new ModuleDecompositionBenchmark();
		
		private final BuchiCegarLoopBenchmarkGenerator m_BenchmarkGenerator;

		


		private static final boolean s_ReduceAbstractionSize = true;
		
		
		private final boolean m_Difference;
		private final boolean m_UseDoubleDeckers;
		private final BInterpolantAutomaton m_InterpolantAutomaton;
		private final boolean m_BouncerStem;
		private final boolean m_BouncerLoop;
		private final boolean m_ScroogeNondeterminismStem;
		private final boolean m_ScroogeNondeterminismLoop;
		private final boolean m_CannibalizeLoop;
		private final int m_MaxNumberOfLoopUnwindings;
		
		private final INTERPOLATION m_Interpolation;
		
		private final RefineBuchi m_RefineBuchi;
		private final List<RefineBuchi.RefinementSetting> m_BuchiRefinementSettingSequence;

		private NonTerminationArgument m_NonterminationArgument;
		
		public NonTerminationArgument getNonTerminationArgument() {
			return m_NonterminationArgument;
		}

		public BuchiCegarLoop(RootNode rootNode,
				SmtManager smtManager,
				TAPreferences taPrefs) {
			this.m_Name = "BuchiCegarLoop";
			this.m_RootNode = rootNode;
			this.m_SmtManager = smtManager;
			this.m_BinaryStatePredicateManager = new BinaryStatePredicateManager(m_SmtManager);
			m_BenchmarkGenerator = new BuchiCegarLoopBenchmarkGenerator();
			m_BenchmarkGenerator.start(BuchiCegarLoopBenchmark.s_OverallTime);
//			this.buchiModGlobalVarManager = new BuchiModGlobalVarManager(
//					m_Bspm.getUnseededVariable(), m_Bspm.getOldRankVariable(), 
//					m_RootNode.getRootAnnot().getModGlobVarManager(),
//					m_RootNode.getRootAnnot().getBoogie2SMT());

			this.m_Pref = taPrefs;
			m_DefaultStateFactory = new PredicateFactory(
					m_SmtManager,
					m_Pref);
			m_PredicateFactoryResultChecking = new PredicateFactoryResultChecking(m_SmtManager);
			
			m_Haf = new HoareAnnotationFragments();
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
			m_Interpolation = baPref.getEnum(TraceAbstractionPreferenceInitializer.LABEL_INTERPOLATED_LOCS, INTERPOLATION.class);
			
			m_RefineBuchi = new RefineBuchi(m_SmtManager, m_Pref.dumpAutomata(), 
					m_Difference, m_DefaultStateFactory, m_StateFactoryForRefinement, m_UseDoubleDeckers, 
					m_Pref.dumpPath(), m_Interpolation);
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
			s_Logger.info("Compute interpolants for " + m_Interpolation);
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
			
			boolean initalAbstractionCorrect;
			try {
				initalAbstractionCorrect = isAbstractionCorrect();
			} catch (OperationCanceledException e1) {
				s_Logger.warn("Verification cancelled");
				m_MDBenchmark.reportRemainderModule(m_Abstraction.size(), false);
				return Result.TIMEOUT;
			}
			if (initalAbstractionCorrect) {
				m_MDBenchmark.reportNoRemainderModule();
				return Result.TERMINATING;
			}
			
			
			
			for (m_Iteration=1; m_Iteration<=m_Pref.maxIterations(); m_Iteration++){
				s_Logger.info("======== Iteration " + m_Iteration + "============");
				m_SmtManager.setIteration(m_Iteration);
				m_BenchmarkGenerator.announceNextIteration();

				boolean abstractionCorrect;
				try {
					abstractionCorrect = isAbstractionCorrect();
				} catch (OperationCanceledException e1) {
					s_Logger.warn("Verification cancelled");
					m_MDBenchmark.reportRemainderModule(m_Abstraction.size(), false);
					return Result.TIMEOUT;
				}
				if (abstractionCorrect) {
					m_MDBenchmark.reportNoRemainderModule();
					return Result.TERMINATING;
				}
				
				m_BenchmarkGenerator.start(BuchiCegarLoopBenchmark.s_LassoAnalysisTime);
				LassoChecker lassoChecker = new LassoChecker(
						m_Interpolation, m_SmtManager, 
						m_RootNode.getRootAnnot().getModGlobVarManager(),
						m_BinaryStatePredicateManager,
						m_Counterexample,
						generateLassoCheckerIdentifier());
				m_BenchmarkGenerator.stop(BuchiCegarLoopBenchmark.s_LassoAnalysisTime);
				

				ContinueDirective cd = lassoChecker.getContinueDirective();
				m_BenchmarkGenerator.reportLassoAnalysis(lassoChecker);
				try {
					switch (cd) {
					case REFINE_BOTH:
					{
						BinaryStatePredicateManager bspm = lassoChecker.getBinaryStatePredicateManager();
						if (bspm.isLoopWithoutStemTerminating()) {
							m_RankWithoutSi++;	
						} else {
							m_RankWithSi++;
						}
						ISLPredicate hondaISLP = (ISLPredicate) m_Counterexample.getLoop().getStateAtPosition(0);
						ProgramPoint hondaPP = hondaISLP.getProgramPoint();
						TerminationArgumentResult<RcfgElement> tar =  
								constructTAResult(bspm.getTerminationArgument(), hondaPP, m_Counterexample.getStem().getWord(), m_Counterexample.getLoop().getWord());
						m_MDBenchmark.reportRankingFunction(m_Iteration, tar);

						INestedWordAutomatonOldApi<CodeBlock, IPredicate> newAbstraction = refineBuchi(lassoChecker);
						m_Abstraction = newAbstraction;
						m_BinaryStatePredicateManager.clearPredicates();
						
						if (s_ReduceAbstractionSize ) {
							reduceAbstractionSize();
						}
						
						refineFinite(lassoChecker);
						m_Infeasible++;
					}
						break;
					case REFINE_FINITE:
						refineFinite(lassoChecker);
						m_Infeasible++;
						break;

					case REFINE_BUCHI:
						BinaryStatePredicateManager bspm = lassoChecker.getBinaryStatePredicateManager();
						if (bspm.isLoopWithoutStemTerminating()) {
							m_RankWithoutSi++;	
						} else {
							m_RankWithSi++;
						}
						ISLPredicate hondaISLP = (ISLPredicate) m_Counterexample.getLoop().getStateAtPosition(0);
						ProgramPoint hondaPP = hondaISLP.getProgramPoint();
						TerminationArgumentResult<RcfgElement> tar =  
								constructTAResult(bspm.getTerminationArgument(), hondaPP, m_Counterexample.getStem().getWord(), m_Counterexample.getLoop().getWord());
						m_MDBenchmark.reportRankingFunction(m_Iteration, tar);
						
						INestedWordAutomatonOldApi<CodeBlock, IPredicate> newAbstraction = refineBuchi(lassoChecker);
						m_Abstraction = newAbstraction;
						m_BinaryStatePredicateManager.clearPredicates();
						break;
					case REPORT_UNKNOWN:
						m_MDBenchmark.reportRemainderModule(m_Abstraction.size(), false);
						return Result.UNKNOWN;
					case REPORT_NONTERMINATION:
						m_NonterminationArgument = lassoChecker.getNonTerminationArgument();
						m_MDBenchmark.reportRemainderModule(m_Abstraction.size(), true);
						return Result.NONTERMINATING;
					default:
						throw new AssertionError("impossible case");
					}
					s_Logger.info("Abstraction has " + m_Abstraction.sizeInformation());
//					s_Logger.info("Interpolant automaton has " + m_RefineBuchi.getInterpolAutomatonUsedInRefinement().sizeInformation());
					
					if (s_ReduceAbstractionSize ) {
						reduceAbstractionSize();
					}


					if (m_Iteration <= m_Pref.watchIteration() && m_Pref.artifact() == Artifact.ABSTRACTION) {
						m_ArtifactAutomaton = m_Abstraction;
					}

					if (m_Pref.dumpAutomata()) {
						String filename = "Abstraction"+m_Iteration;
						writeAutomatonToFile(m_Abstraction, m_Pref.dumpPath(), filename);
					}
					m_BenchmarkGenerator.reportAbstractionSize(m_Abstraction.size(), m_Iteration);

				} catch (AutomataLibraryException e) {
					return Result.TIMEOUT;
				}
				m_InterpolAutomaton = null;
			}
			return Result.TIMEOUT;
		}

		/**
		 * @throws OperationCanceledException
		 * @throws AutomataLibraryException
		 * @throws AssertionError
		 */
		private void reduceAbstractionSize() throws OperationCanceledException,
				AutomataLibraryException, AssertionError {
			m_BenchmarkGenerator.start(BuchiCegarLoopBenchmark.s_NonLiveStateRemoval);
			try {
				m_Abstraction = (new RemoveNonLiveStates<CodeBlock, IPredicate>(m_Abstraction)).getResult();
			} finally {
				m_BenchmarkGenerator.stop(BuchiCegarLoopBenchmark.s_NonLiveStateRemoval);
			}
			m_BenchmarkGenerator.start(BuchiCegarLoopBenchmark.s_BuchiClosure);
			try {
				m_Abstraction = (INestedWordAutomatonOldApi<CodeBlock, IPredicate>) (new BuchiClosureNwa(m_Abstraction));
				m_Abstraction = (new RemoveDeadEnds<CodeBlock, IPredicate>(m_Abstraction)).getResult();
			} finally {
				m_BenchmarkGenerator.stop(BuchiCegarLoopBenchmark.s_BuchiClosure);
			}
			m_BenchmarkGenerator.start(CegarLoopBenchmarkType.s_AutomataMinimizationTime);
			int statesBeforeMinimization = m_Abstraction.size();
			s_Logger.info("Abstraction has " + m_Abstraction.sizeInformation());
			Collection<Set<IPredicate>> partition = BuchiCegarLoop.computePartition(m_Abstraction);
			MinimizeSevpa<CodeBlock, IPredicate> minimizeOp = 
					new MinimizeSevpa<CodeBlock, IPredicate>(m_Abstraction, partition, false, false, m_StateFactoryForRefinement);
			assert (minimizeOp.checkResult(m_PredicateFactoryResultChecking));
			INestedWordAutomatonOldApi<CodeBlock, IPredicate> minimized = minimizeOp.getResult();
			m_Abstraction = minimized;
			int statesAfterMinimization = m_Abstraction.size();
			m_BenchmarkGenerator.announceStatesRemovedByMinimization(statesBeforeMinimization - statesAfterMinimization);
			s_Logger.info("Abstraction has " + m_Abstraction.sizeInformation());
			m_BenchmarkGenerator.stop(CegarLoopBenchmarkType.s_AutomataMinimizationTime);
		}
		
		private INestedWordAutomatonOldApi<CodeBlock, IPredicate> refineBuchi(LassoChecker lassoChecker) throws AutomataLibraryException {
			m_BenchmarkGenerator.start(CegarLoopBenchmarkType.s_AutomataDifference);
			int stage = 0;
			BuchiModGlobalVarManager bmgvm = new BuchiModGlobalVarManager(
					lassoChecker.getBinaryStatePredicateManager().getUnseededVariable(), 
					lassoChecker.getBinaryStatePredicateManager().getOldRankVariables(), 
					m_RootNode.getRootAnnot().getModGlobVarManager(),
					m_RootNode.getRootAnnot().getBoogie2SMT());
			for (RefinementSetting rs : m_BuchiRefinementSettingSequence) {
//				if (stage > 0) {
//					s_Logger.info("Statistics: We needed stage " + stage);
//				}
				INestedWordAutomatonOldApi<CodeBlock, IPredicate> newAbstraction = null;
				try {
					newAbstraction = m_RefineBuchi.refineBuchi(m_Abstraction, m_Counterexample, 
								m_Iteration, rs, lassoChecker.getBinaryStatePredicateManager(), 
								bmgvm, m_Interpolation, m_BenchmarkGenerator);
				} catch (OperationCanceledException e) {
					m_BenchmarkGenerator.stop(CegarLoopBenchmarkType.s_AutomataDifference);
					throw e;
				}
				if (newAbstraction != null) {
					m_BenchmarkGenerator.announceSuccessfullRefinementStage(stage);
					switch (rs.getInterpolantAutomaton()) {
					case Deterministic:
					case LassoAutomaton:
						m_MDBenchmark.reportDeterminsticModule(m_Iteration,m_RefineBuchi.getInterpolAutomatonUsedInRefinement().size());
						break;
					case ScroogeNondeterminism:
					case EagerNondeterminism:
						m_MDBenchmark.reportNonDeterminsticModule(m_Iteration,m_RefineBuchi.getInterpolAutomatonUsedInRefinement().size());
						break;
					default:
						throw new AssertionError("unsupported");
					}
					m_BenchmarkGenerator.stop(CegarLoopBenchmarkType.s_AutomataDifference);
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
		
		

		
		private void refineFinite(LassoChecker lassoChecker) throws OperationCanceledException {
			m_BenchmarkGenerator.start(CegarLoopBenchmarkType.s_AutomataDifference);
			final TraceChecker traceChecker;
			final NestedRun<CodeBlock, IPredicate> run;
			if (lassoChecker.isStemInfeasible()) {
				// if both (stem and loop) are infeasible we take the smaller
				// one.
				int stemSize = m_Counterexample.getStem().getLength();
				int loopSize = m_Counterexample.getLoop().getLength();
				if (lassoChecker.isLoopInfeasible() && loopSize <= stemSize) {
					traceChecker = lassoChecker.getLoopCheck();
					run = m_Counterexample.getLoop();
				} else {
					traceChecker = lassoChecker.getStemCheck();
					run = m_Counterexample.getStem();
				}
			} else if (lassoChecker.isLoopInfeasible()) {
				traceChecker = lassoChecker.getLoopCheck();
				run = m_Counterexample.getLoop();
			} else {
				assert lassoChecker.isConcatInfeasible();
				traceChecker = lassoChecker.getConcatCheck();
				run = lassoChecker.getConcatenatedCounterexample();
			}
			constructInterpolantAutomaton(traceChecker, run);
			EdgeChecker ec = new EdgeChecker(m_SmtManager, m_RootNode.getRootAnnot().getModGlobVarManager());
			boolean computeHoareAnnotation = false;
			PostDeterminizer spd = new PostDeterminizer(
					ec, computeHoareAnnotation, m_InterpolAutomaton, true, m_DefaultStateFactory);
			DifferenceDD<CodeBlock, IPredicate> diff = null;
			try {
				diff = new DifferenceDD<CodeBlock, IPredicate>(
						m_Abstraction, m_InterpolAutomaton, spd, 
						m_StateFactoryForRefinement,
						false, true);
			} catch (AutomataLibraryException e) {
				if (e instanceof OperationCanceledException) {
					m_BenchmarkGenerator.stop(CegarLoopBenchmarkType.s_AutomataDifference);
					throw (OperationCanceledException) e;
				} else {
					throw new AssertionError();
				}
			}
			if (m_Pref.dumpAutomata()) {
				String filename = "interpolAutomatonUsedInRefinement"+m_Iteration+"after";
				writeAutomatonToFile(m_InterpolAutomaton, m_Pref.dumpPath(), filename);
			}
			m_MDBenchmark.reportTrivialModule(m_Iteration,m_InterpolAutomaton.size());
			assert (new InductivityCheck(m_InterpolAutomaton, ec, false, true)).getResult();
			m_Abstraction = diff.getResult();
			m_BenchmarkGenerator.addEdgeCheckerData(ec.getEdgeCheckerBenchmark());
			m_BenchmarkGenerator.stop(CegarLoopBenchmarkType.s_AutomataDifference);
		}
		
		protected void constructInterpolantAutomaton(TraceChecker traceChecker, NestedRun<CodeBlock, IPredicate> run) throws OperationCanceledException {
			InterpolantAutomataBuilder iab = new InterpolantAutomataBuilder(
							run,
							traceChecker,
							m_Pref.interpolantAutomaton(), m_Pref.edges2True(),
							m_SmtManager,
							m_Iteration, null);
			m_InterpolAutomaton = iab.buildInterpolantAutomaton(
					m_Abstraction, m_Abstraction.getStateFactory());
			
			assert((new Accepts<CodeBlock, IPredicate>(m_InterpolAutomaton, run.getWord())).getResult()) :
				"Interpolant automaton broken!";
//			assert((new BuchiAccepts<CodeBlock, IPredicate>(m_InterpolAutomaton, m_Counterexample.getNestedLassoWord())).getResult()) :
//				"Interpolant automaton broken!";
			assert (m_SmtManager.checkInductivity(m_InterpolAutomaton, false, true));
		}
		
		
		

		
		private TerminationArgumentResult<RcfgElement> constructTAResult(
				TerminationArgument terminationArgument, 
				ProgramPoint honda, NestedWord<CodeBlock> stem,
				NestedWord<CodeBlock> loop) {
			RankingFunction rf = terminationArgument.getRankingFunction();
			Collection<SupportingInvariant> si_list = terminationArgument.getSupportingInvariants();
			Expression[] supporting_invariants = new Expression[si_list.size()];
			int i = 0;
			for (SupportingInvariant si : terminationArgument.getSupportingInvariants()) {
				supporting_invariants[i] = si.asExpression(m_SmtManager.getScript(), m_RootNode.getRootAnnot().getBoogie2SMT().getTerm2Expression());
				++i;
			}
			TerminationArgumentResult<RcfgElement> result = 
					new TerminationArgumentResult<RcfgElement>(
							honda,
							Activator.s_PLUGIN_NAME,
							rf.asLexExpression(m_SmtManager.getScript(), m_RootNode.getRootAnnot().getBoogie2SMT().getTerm2Expression()),
							rf.getName(),
							supporting_invariants,
							UltimateServices.getInstance().getTranslatorSequence()
							);
			return result;
		}

//		private void reportTerminationArgument(
//				TerminationArgument terminationArgument, 
//				ProgramPoint honda, NestedWord<CodeBlock> stem,
//				NestedWord<CodeBlock> loop) {
//			RankingFunction rf = terminationArgument.getRankingFunction();
//			Collection<SupportingInvariant> si_list = terminationArgument.getSupportingInvariants();
//			Expression[] supporting_invariants = new Expression[si_list.size()];
//			int i = 0;
//			for (SupportingInvariant si : terminationArgument.getSupportingInvariants()) {
//				supporting_invariants[i] = si.asExpression(m_SmtManager.getScript(), m_SmtManager.getSmt2Boogie());
//				++i;
//			}
//			TerminationArgumentResult<RcfgElement> result = 
//					new TerminationArgumentResult<RcfgElement>(
//							honda,
//							Activator.s_PLUGIN_NAME,
//							rf.asLexExpression(m_SmtManager.getScript(), m_SmtManager.getSmt2Boogie()),
//							rf.getClass().getName(),
//							supporting_invariants,
//							UltimateServices.getInstance().getTranslatorSequence(),
//							honda.getPayload().getLocation()
//							);
//			BuchiAutomizerObserver.reportResult(result);
//		}
		
		
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


		public ModuleDecompositionBenchmark getMDBenchmark() {
			return m_MDBenchmark;
		}

		/**
		 * Returns an Identifier that describes a lasso analysis.
		 * Right now, this is the Filename (without path prefix) of analyzed
		 * file together with the number of the current iteration.
		 * 
		 */
		public String generateLassoCheckerIdentifier() {
			String pureFilename = m_RootNode.getFilename();
			return pureFilename + "_Iteration" + m_Iteration;
		}

		public BuchiCegarLoopBenchmarkGenerator getBenchmarkGenerator() {
			return m_BenchmarkGenerator;
		}
	
		

		
}
