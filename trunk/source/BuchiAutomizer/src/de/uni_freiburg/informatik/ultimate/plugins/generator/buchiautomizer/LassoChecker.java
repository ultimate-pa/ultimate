package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.LassoRankerTerminationAnalysis;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.NonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.SupportingInvariant;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.TerminationArgument;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.Preferences;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.AffineTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.LexicographicTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.MultiphaseTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.PiecewiseTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.RankingFunctionTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerSpWp;


public class LassoChecker {

	private final static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	enum ContinueDirective { REFINE_FINITE, REFINE_BUCHI, REPORT_NONTERMINATION, REPORT_UNKNOWN, REFINE_BOTH }
	enum SynthesisResult { TERMINATING, NONTERMINATIG, UNKNOWN, UNCHECKED }
	
	//////////////////////////////// settings /////////////////////////////////
	
	private static final boolean m_SimplifyStemAndLoop = true;
	/**
	 * If true we check if the loop has a ranking function even if the stem
	 * or the concatenation of stem and loop are already infeasible.
	 * If false we make this additional check only if the loop is smaller than
	 * the stem.
	 */
	private static final boolean s_AlwaysAdditionalLoopTerminationCheck = true;
	
	private final INTERPOLATION m_Interpolation;
	
	/**
	 * Use an external solver. If false, we use SMTInterpol.
	 */
	private boolean m_ExternalSolver_RankSynthesis;
	/**
	 * Command of external solver.
	 */
	private final String m_ExternalSolverCommand_RankSynthesis;
	private final boolean m_AllowNonLinearConstraints;
	
	/**
	 * Try all templates but use the one that was found first. This is only
	 * useful to test all templates at once.  
	 */
	private final boolean m_TemplateBenchmarkMode;
	
	//////////////////////////////// input /////////////////////////////////
	/**
	 * Intermediate layer to encapsulate communication with SMT solvers. 
	 */
	private final SmtManager m_SmtManager;
	
	private final ModifiableGlobalVariableManager m_ModifiableGlobalVariableManager;
	
	private final BinaryStatePredicateManager m_Bspm;
	
	/**
	 * Accepting run of the abstraction obtained in this iteration. 
	 */
	private final NestedLassoRun<CodeBlock, IPredicate> m_Counterexample;
	
	
	//////////////////////////////// auxilliary variables //////////////////////
	
	private final IPredicate m_TruePredicate;
	private final IPredicate m_FalsePredicate;
	
	//////////////////////////////// output /////////////////////////////////

//	private final BuchiModGlobalVarManager m_BuchiModGlobalVarManager;
	
	private final PredicateUnifier m_PredicateUnifier;
	
	private Boolean m_StemInfeasible;
	private TraceChecker m_StemCheck;
	private Boolean m_LoopInfeasible;
	private TraceChecker m_LoopCheck;
	private Boolean m_ConcatInfeasible;
	private TraceChecker m_ConcatCheck;
	
	private NestedRun<CodeBlock, IPredicate> m_ConcatenatedCounterexample;
	
	
	
	private ContinueDirective m_ContinueDirective;

	private SynthesisResult m_LoopTermination = SynthesisResult.UNCHECKED;
	private SynthesisResult m_LassoTermination = SynthesisResult.UNCHECKED;
	
	private NonTerminationArgument m_NonterminationArgument;

	
	public ContinueDirective getContinueDirective() {
		assert m_ContinueDirective != null;
		return m_ContinueDirective;
	}
	
	public boolean isStemInfeasible() {
		return m_StemInfeasible;
	}
	
	public TraceChecker getStemCheck() {
		return m_StemCheck;
	}
	
	public boolean isLoopInfeasible() {
		return m_LoopInfeasible;
	}
	
	public TraceChecker getLoopCheck() {
		return m_LoopCheck;
	}

	public boolean isConcatInfeasible() {
		return m_ConcatInfeasible;
	}

	public TraceChecker getConcatCheck() {
		return m_ConcatCheck;
	}

	public NestedRun<CodeBlock, IPredicate> getConcatenatedCounterexample() {
		assert m_ConcatenatedCounterexample != null;
		return m_ConcatenatedCounterexample;
	}

	public BinaryStatePredicateManager getBinaryStatePredicateManager() {
		return m_Bspm;
	}
	
	public NonTerminationArgument getNonTerminationArgument() {
		return m_NonterminationArgument;
	}


	public LassoChecker(INTERPOLATION interpolation, SmtManager smtManager,
			ModifiableGlobalVariableManager modifiableGlobalVariableManager,
			BinaryStatePredicateManager bspm,
			NestedLassoRun<CodeBlock, IPredicate> counterexample) {
		super();
		UltimatePreferenceStore baPref = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		m_ExternalSolver_RankSynthesis = baPref.getBoolean(PreferenceInitializer.LABEL_ExtSolverRank);
		m_ExternalSolverCommand_RankSynthesis = baPref.getString(PreferenceInitializer.LABEL_ExtSolverCommandRank);
		m_AllowNonLinearConstraints = baPref.getBoolean(PreferenceInitializer.LABEL_NonLinearConstraints);
		m_TemplateBenchmarkMode = baPref.getBoolean(PreferenceInitializer.LABEL_TemplateBenchmarkMode);
		m_Interpolation = interpolation;
		m_SmtManager = smtManager;
		m_ModifiableGlobalVariableManager = modifiableGlobalVariableManager;
		m_Bspm = bspm;
		m_Counterexample = counterexample;
		m_TruePredicate = m_SmtManager.newTruePredicate();
		m_FalsePredicate = m_SmtManager.newFalsePredicate();
		m_PredicateUnifier = new PredicateUnifier(m_SmtManager, m_TruePredicate, m_FalsePredicate);
		checkFeasibility();
		assert m_ContinueDirective != null;
		assert m_StemInfeasible != null;
		assert m_LoopInfeasible != null;
		if (m_StemInfeasible) {
			assert m_ContinueDirective == ContinueDirective.REFINE_FINITE || 
					m_ContinueDirective == ContinueDirective.REFINE_BOTH;
		} else {
			if (m_LoopInfeasible) {
				assert m_ContinueDirective == ContinueDirective.REFINE_FINITE;
			} else {
				if (m_ConcatInfeasible == null) {
					assert m_Bspm.providesPredicates();
				} else {
					assert m_ConcatCheck != null;
					if (m_ConcatInfeasible) {
						assert m_ContinueDirective == ContinueDirective.REFINE_FINITE || 
								m_ContinueDirective == ContinueDirective.REFINE_BOTH;
						assert m_ConcatenatedCounterexample != null;
					} else {
						assert m_ContinueDirective != ContinueDirective.REFINE_FINITE;
					}
				}
			}
		}
	}


	
	private void checkFeasibility() {
		NestedRun<CodeBlock, IPredicate> stem = m_Counterexample.getStem();
		s_Logger.info("Stem: " + stem);
		NestedRun<CodeBlock, IPredicate> loop = m_Counterexample.getLoop();
		s_Logger.info("Loop: " + loop);
		checkStemFeasibility();
		if (m_StemInfeasible) {
			s_Logger.info("stem already infeasible");
		}
		checkLoopFeasibility();
		if (m_LoopInfeasible) {
			s_Logger.info("loop already infeasible");
			m_ContinueDirective = ContinueDirective.REFINE_FINITE;
			return;
		} else {
			TransFormula loopTF = computeLoopTF();
			checkLoopTermination(loopTF);
			if (m_LoopTermination == SynthesisResult.TERMINATING) {
				if (m_StemInfeasible) {
					m_ContinueDirective = ContinueDirective.REFINE_BOTH;
					return;
				} else {
					checkConcatFeasibility();
					if (m_ConcatInfeasible) {
						m_ContinueDirective = ContinueDirective.REFINE_BOTH;
						return;
					} else {
						m_ContinueDirective = ContinueDirective.REFINE_BUCHI;
						return;
					}
				}
			} else {
				if (m_StemInfeasible) {
					m_ContinueDirective = ContinueDirective.REFINE_FINITE;
					return;
				} else {
					checkConcatFeasibility();
					if (m_ConcatInfeasible) {
						m_ContinueDirective = ContinueDirective.REFINE_FINITE;
						return;
					} else {
						TransFormula stemTF = computeStemTF();
						checkLassoTermination(stemTF, loopTF);
						if (m_LassoTermination == SynthesisResult.TERMINATING) {
							m_ContinueDirective = ContinueDirective.REFINE_BUCHI;
							return;
						} else if (m_LassoTermination == SynthesisResult.NONTERMINATIG) {
							m_ContinueDirective = ContinueDirective.REPORT_NONTERMINATION;
							return;
						} else {
							m_ContinueDirective = ContinueDirective.REPORT_UNKNOWN;
							return;
						}
					}
				}
			}
		}
		
//			if (s_AlwaysAdditionalLoopTerminationCheck ||
//					loop.getLength() < stem.getLength()) {
//				TransFormula loopTF = computeLoopTF();
//				checkLoopTermination(loopTF);
//				if (m_LoopTermination == SynthesisResult.TERMINATING) {
//					m_ContinueDirective = ContinueDirective.REFINE_BOTH;
//					return;
//				} else {
//					m_ContinueDirective = ContinueDirective.REFINE_FINITE;
//					return;
//				}
//			} else {
//				m_ContinueDirective = ContinueDirective.REFINE_FINITE;
//				return;
//			}
//		} else {
//			checkLoopFeasibility();
//			if (m_LoopInfeasible) {
//				s_Logger.info("loop already infeasible");
////				// because BuchiCegarLoop can not continue with the loop
////				// compute this information for concat.
////				// TODO: this is a hack find better solution
////				checkConcatFeasibility();
////				if (!m_ConcatInfeasible) {
////					throw new AssertionError("stem infeasible, loop" +
////						" infeasible but not concat? If this happens there is" +
////						" a bug or there some problem with UNKNOWN that is" +
////						" not implemented yet.");
////				}
//				m_ContinueDirective = ContinueDirective.REFINE_FINITE;
//				return;
//			} else {
//				checkConcatFeasibility();
//				if (m_ConcatInfeasible) {
//					s_Logger.info("concat infeasible");
//					if (s_AlwaysAdditionalLoopTerminationCheck || 
//							loop.getLength() < stem.getLength()) {
//						TransFormula loopTF = computeLoopTF();
//						checkLoopTermination(loopTF);
//						if (m_LoopTermination == SynthesisResult.TERMINATING) {
//							m_ContinueDirective = ContinueDirective.REFINE_BOTH;
//							return;
//						} else {
//							m_ContinueDirective = ContinueDirective.REFINE_FINITE;
//							return;
//						}
//					} else {
//						m_ContinueDirective = ContinueDirective.REFINE_FINITE;
//						return;
//					}
//				} else {
//					TransFormula loopTF = computeLoopTF();
//					checkLoopTermination(loopTF);
//				if (m_LoopTermination == SynthesisResult.TERMINATING) {
//					m_ContinueDirective = ContinueDirective.REFINE_BUCHI;
//					return;
//				} else {
//
//						TransFormula stemTF = computeStemTF();
//						checkLassoTermination(stemTF, loopTF);
//						if (m_LassoTermination == SynthesisResult.TERMINATING) {
//							m_ContinueDirective = ContinueDirective.REFINE_BUCHI;
//							return;
//						} else if (m_LassoTermination == SynthesisResult.NONTERMINATIG) {
//							m_ContinueDirective = ContinueDirective.REPORT_NONTERMINATION;
//							return;
//						} else {
//							m_ContinueDirective = ContinueDirective.REPORT_UNKNOWN;
//							return;
//						}
//					}
//					
//				}
//			}
//		}
		 // boolean thisCodeShouldBeUnreachalbe = true;
	}
	
	private void checkStemFeasibility() {
		NestedRun<CodeBlock, IPredicate> stem = m_Counterexample.getStem();
		if (BuchiCegarLoop.emptyStem(m_Counterexample)) {
			m_StemInfeasible = false;
		} else {
			m_StemCheck = checkFeasibilityAndComputeInterpolants(stem);
			if (m_StemCheck.isCorrect() == LBool.UNSAT) {
				m_StemInfeasible = true;
			} else {
				m_StemInfeasible = false;
			}
		}
	}
	
	private void checkLoopFeasibility() {
		NestedRun<CodeBlock, IPredicate> loop = m_Counterexample.getLoop();
		m_LoopCheck = checkFeasibilityAndComputeInterpolants(loop);
		if (m_LoopCheck.isCorrect() == LBool.UNSAT) {
			m_LoopInfeasible = true;
		} else {
			m_LoopInfeasible = false;
		}		
	}
	
	private void checkConcatFeasibility() {
		NestedRun<CodeBlock, IPredicate> stem = m_Counterexample.getStem();
		NestedRun<CodeBlock, IPredicate> loop = m_Counterexample.getLoop();
		NestedRun<CodeBlock, IPredicate> concat = stem.concatenate(loop);
		m_ConcatCheck = checkFeasibilityAndComputeInterpolants(concat);
		if (m_ConcatCheck.isCorrect() == LBool.UNSAT) {
			m_ConcatInfeasible = true;
			m_ConcatenatedCounterexample = concat;
		} else {
			m_ConcatInfeasible = false;
		}		
	}
	
	
	
	
	
	
	private TraceChecker checkFeasibilityAndComputeInterpolants(
			NestedRun<CodeBlock, IPredicate> run) {
		TraceChecker result;
		switch (m_Interpolation) {
		case Craig_NestedInterpolation:
		case Craig_TreeInterpolation:
			result = new TraceChecker(m_TruePredicate, m_FalsePredicate, 
					null, run.getWord(),m_SmtManager,
					m_ModifiableGlobalVariableManager);
			break;
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP:
			result = new TraceCheckerSpWp(m_TruePredicate, m_FalsePredicate, 
					run.getWord(),m_SmtManager,
					m_ModifiableGlobalVariableManager);
			break;
		default:
			throw new UnsupportedOperationException("unsupported interpolation");
		}
		if (result.isCorrect() == LBool.UNSAT) {
				result.computeInterpolants(new TraceChecker.AllIntegers(), 
						m_PredicateUnifier, m_Interpolation);
		} else {
			result.finishTraceCheckWithoutInterpolantsOrProgramExecution();
		}
		return result;
	}
	
	
	
	private void checkLoopTermination(TransFormula loopTF) {
		assert !m_Bspm.providesPredicates() : "termination already checked";
		m_LoopTermination = synthesize(false, null, loopTF);
	}


	
	private void checkLassoTermination(TransFormula stemTF, TransFormula loopTF) {
		assert !m_Bspm.providesPredicates() : "termination already checked";
		assert loopTF != null;
		m_LassoTermination = synthesize(true, stemTF, loopTF);
	}

	/**
	 * Compute TransFormula that represents the stem.
	 */
	protected TransFormula computeStemTF() {
		NestedWord<CodeBlock> stem = m_Counterexample.getStem().getWord();
		TransFormula stemTF = computeTF(stem, m_SimplifyStemAndLoop, true, false);
		return stemTF;
	}
	
	/**
	 * Compute TransFormula that represents the loop.
	 */
	protected TransFormula computeLoopTF() {
		NestedWord<CodeBlock> loop = m_Counterexample.getLoop().getWord();
		TransFormula loopTF = computeTF(loop, m_SimplifyStemAndLoop, true, false);
		return loopTF;
	}
	
	/**
	 * Compute TransFormula that represents the NestedWord word.
	 */
	private TransFormula computeTF(NestedWord<CodeBlock> word, 
			boolean simplify, boolean extendedPartialQuantifierElimination, 
			boolean withBranchEncoders) {
		CodeBlock[] cbs = new CodeBlock[word.length()];
		for (int i=0; i<word.length(); i++) {
			cbs[i] = word.getSymbol(i);
		}
		TransFormula loopTF = SequentialComposition.getInterproceduralTransFormula(
				m_SmtManager.getBoogie2Smt(),
				m_ModifiableGlobalVariableManager,
				simplify, extendedPartialQuantifierElimination, 
				withBranchEncoders, cbs);
		return loopTF;
	}
	
	
	private boolean areSupportingInvariantsCorrect() {
		NestedWord<CodeBlock> stem = m_Counterexample.getStem().getWord();
		s_Logger.info("Stem: " + stem);
		NestedWord<CodeBlock> loop = m_Counterexample.getLoop().getWord();
		s_Logger.info("Loop: " + loop);
		boolean siCorrect = true;
		if (stem.length() == 0) {
			// do nothing
			// TODO: check that si is equivalent to true
		} else {
			for (SupportingInvariant si : m_Bspm.getTerminationArgument().getSupportingInvariants()) {
				siCorrect &= m_Bspm.checkSupportingInvariant(
						si, stem, loop, m_ModifiableGlobalVariableManager);
			}
		}
		return siCorrect;
	}
	
	private boolean isRankingFunctionCorrect() {
		NestedWord<CodeBlock> loop = m_Counterexample.getLoop().getWord();
		s_Logger.info("Loop: " + loop);
		boolean rfCorrect = m_Bspm.checkRankDecrease(loop, m_ModifiableGlobalVariableManager);
		return rfCorrect;
	}
	
	private SynthesisResult synthesize(final boolean withStem, TransFormula stemTF, final TransFormula loopTF) {
		if (!withStem) {
			stemTF = getDummyTF();
		}
		int loopVars = loopTF.getFormula().getFreeVars().length;
		if (stemTF == null) {
			s_Logger.info("Statistics: no stem, loopVars: " + loopVars);
		} else {
			int stemVars = stemTF.getFormula().getFreeVars().length;
			s_Logger.info("Statistics: stemVars: " + stemVars + "loopVars: " + loopVars);
		}
		
		Preferences pref = new Preferences();
		pref.num_non_strict_invariants = 1;
		pref.num_strict_invariants = 0;
		pref.only_nondecreasing_invariants = true;
		pref.externalSolver = m_ExternalSolver_RankSynthesis;
		pref.smt_solver_command = m_ExternalSolverCommand_RankSynthesis;
		pref.nontermination_check_nonlinear = m_AllowNonLinearConstraints;
		pref.termination_check_nonlinear = m_AllowNonLinearConstraints;

		LassoRankerTerminationAnalysis lrta = null;
		try {
			 lrta =	new LassoRankerTerminationAnalysis(m_SmtManager.getScript(), m_SmtManager.getBoogie2Smt(), stemTF, loopTF, pref);
		} catch (TermException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			throw new AssertionError("TermException " + e);
		}
		NonTerminationArgument nonTermArgument = lrta.checkNonTermination();
		if (withStem) {
			m_NonterminationArgument = nonTermArgument;
		}
		
		List<RankingFunctionTemplate> rankingFunctionTemplates = 
				new ArrayList<RankingFunctionTemplate>();
		rankingFunctionTemplates.add(new AffineTemplate());
		
		if (m_AllowNonLinearConstraints) {
			rankingFunctionTemplates.add(new MultiphaseTemplate(1));
			rankingFunctionTemplates.add(new MultiphaseTemplate(2));
			rankingFunctionTemplates.add(new MultiphaseTemplate(3));
			rankingFunctionTemplates.add(new MultiphaseTemplate(4));
			rankingFunctionTemplates.add(new MultiphaseTemplate(5));
			rankingFunctionTemplates.add(new MultiphaseTemplate(6));
			rankingFunctionTemplates.add(new MultiphaseTemplate(7));

			rankingFunctionTemplates.add(new LexicographicTemplate(1));
			rankingFunctionTemplates.add(new LexicographicTemplate(2));
			rankingFunctionTemplates.add(new LexicographicTemplate(3));
			rankingFunctionTemplates.add(new LexicographicTemplate(4));
			
			rankingFunctionTemplates.add(new PiecewiseTemplate(2));
			rankingFunctionTemplates.add(new PiecewiseTemplate(3));
		}

		TerminationArgument termArg = tryTemplatesAndComputePredicates(
				withStem, lrta, rankingFunctionTemplates);
		assert (nonTermArgument == null || termArg == null) : " terminating and nonterminating";
		if (termArg != null) {
			return SynthesisResult.TERMINATING;
		} else if (nonTermArgument != null) {
			return SynthesisResult.NONTERMINATIG;
		} else {
			return SynthesisResult.UNKNOWN;
		}
	}

	/**
	 * @param withStem
	 * @param lrta
	 * @param nonTermArgument
	 * @param rankingFunctionTemplates
	 * @return
	 * @throws AssertionError
	 */
	private TerminationArgument tryTemplatesAndComputePredicates(
			final boolean withStem, LassoRankerTerminationAnalysis lrta,
			List<RankingFunctionTemplate> rankingFunctionTemplates)
			throws AssertionError {
		TerminationArgument firstTerminationArgument = null;
		for (RankingFunctionTemplate rft : rankingFunctionTemplates) {
			TerminationArgument termArg;
			try {
				termArg = lrta.tryTemplate(rft);
			} catch (SMTLIBException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
				throw new AssertionError("SMTLIBException " + e);
			} catch (TermException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
				throw new AssertionError("TermException " + e);
			}
			if (termArg != null) {
				assert termArg.getRankingFunction() != null;
				assert termArg.getSupportingInvariants() != null;
				m_Bspm.computePredicates(!withStem, termArg);
				assert m_Bspm.providesPredicates();
				assert areSupportingInvariantsCorrect() : 
					"incorrect supporting invariant with" + rft.getClass().getSimpleName();
				assert isRankingFunctionCorrect() : 
					"incorrect ranking function with" + rft.getClass().getSimpleName();
				if (!m_TemplateBenchmarkMode) {
					return termArg;
				} else {
					if (firstTerminationArgument == null) {
						firstTerminationArgument = termArg;
					}
				}
				m_Bspm.clearPredicates();
			}
		}
		if (firstTerminationArgument != null) {
			assert firstTerminationArgument.getRankingFunction() != null;
			assert firstTerminationArgument.getSupportingInvariants() != null;
			m_Bspm.computePredicates(!withStem, firstTerminationArgument);
			assert m_Bspm.providesPredicates();
			return firstTerminationArgument;
		} else {
			return null;
		}
	}
	
//	private List<LassoRankerParam> getLassoRankerParameters() {
//		List<LassoRankerParam> lassoRankerParams = new ArrayList<LassoRankerParam>();
//		Preferences pref = new Preferences();
//		pref.num_non_strict_invariants = 2;
//		pref.num_strict_invariants = 0;
//		pref.only_nondecreasing_invariants = false;
//		lassoRankerParams.add(new LassoRankerParam(new AffineTemplate(), pref));
//		return lassoRankerParams;
//	}
	
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
	
//	private class LassoRankerParam {
//		private final RankingFunctionTemplate m_RankingFunctionTemplate;
//		private final Preferences m_Preferences;
//		public LassoRankerParam(RankingFunctionTemplate rankingFunctionTemplate,
//				Preferences preferences) {
//			super();
//			this.m_RankingFunctionTemplate = rankingFunctionTemplate;
//			this.m_Preferences = preferences;
//		}
//		public RankingFunctionTemplate getRankingFunctionTemplate() {
//			return m_RankingFunctionTemplate;
//		}
//		public Preferences getPreferences() {
//			return m_Preferences;
//		}
//	}
	
	
}
