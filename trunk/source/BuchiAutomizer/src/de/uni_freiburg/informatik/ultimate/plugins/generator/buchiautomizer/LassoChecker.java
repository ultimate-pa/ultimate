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
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preferences.Preferences;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.AffineTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.MultiphaseTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.RankingFunctionTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.PreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerSpWp;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;

public class LassoChecker {

	private final static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	enum ContinueDirective { REFINE_FINITE, REFINE_BUCHI, REPORT_NONTERMINATION, REPORT_UNKNOWN }
	enum SynthesisResult { TERMINATING, NONTERMINATIG, UNKNOWN, UNCHECKED }
	
	//////////////////////////////// settings /////////////////////////////////
	
	private static final boolean m_SimplifyStemAndLoop = true;
	private static final boolean m_ExternalSolver = false;
	
	private final INTERPOLATION m_Interpolation;

	
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


	public LassoChecker(INTERPOLATION interpolation, SmtManager smtManager,
			ModifiableGlobalVariableManager modifiableGlobalVariableManager,
			BinaryStatePredicateManager bspm,
			NestedLassoRun<CodeBlock, IPredicate> counterexample) {
		super();
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
		if (!m_StemInfeasible) {
			if (m_ConcatInfeasible == null) {
				assert m_Bspm.providesPredicates();
			} else {
				assert m_ConcatCheck != null;
				if (m_ConcatInfeasible) {
					assert m_ContinueDirective == ContinueDirective.REFINE_FINITE;
					assert m_ConcatenatedCounterexample != null;
				} else {
					assert m_ContinueDirective != ContinueDirective.REFINE_FINITE;
					
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
			if (loop.getLength() < stem.getLength()) {
				TransFormula loopTF = computeLoopTF();
				checkLoopTermination(loopTF);
				if (m_LoopTermination == SynthesisResult.TERMINATING) {
					m_ContinueDirective = ContinueDirective.REFINE_BUCHI;
					return;
				} else {
					m_ContinueDirective = ContinueDirective.REFINE_FINITE;
					return;
				}
			} else {
				m_ContinueDirective = ContinueDirective.REFINE_FINITE;
				return;
			}
		} else {
			checkLoopFeasibility();
			if (m_LoopInfeasible) {
				s_Logger.info("loop already infeasible");
				// because BuchiCegarLoop can not continue with the loop
				// compute this information for concat.
				// TODO: this is a hack find better solution
				checkConcatFeasibility();
				if (!m_ConcatInfeasible) {
					throw new AssertionError("stem infeasible, loop" +
						" infeasible but not concat? If this happens there is" +
						" a bug or there some problem with UNKNOWN that is" +
						" not implemented yet.");
				}
				m_ContinueDirective = ContinueDirective.REFINE_FINITE;
				return;
			} else {
				checkConcatFeasibility();
				if (m_ConcatInfeasible) {
					s_Logger.info("concat infeasible");
					m_ContinueDirective = ContinueDirective.REFINE_FINITE;
					return;
				} else {
					// check termination
					TransFormula loopTF = computeLoopTF();
					checkLoopTermination(loopTF);
					if (m_LoopTermination == SynthesisResult.TERMINATING) {
						m_ContinueDirective = ContinueDirective.REFINE_BUCHI;
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
		case FPandSP:
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
		int stemVars = stemTF.getFormula().getFreeVars().length;
		int loopVars = loopTF.getFormula().getFreeVars().length;
		s_Logger.info("Statistics: stemVars: " + stemVars + "loopVars: " + loopVars);
		
		Preferences pref = new Preferences();
		pref.num_non_strict_invariants = 2;
		pref.num_strict_invariants = 0;
		pref.only_nondecreasing_invariants = false;
		pref.smt_solver_command = "z3 -smt2 -in -t:20";

		LassoRankerTerminationAnalysis lrta = null;
		try {
			 lrta =	new LassoRankerTerminationAnalysis(m_SmtManager.getScript(), m_SmtManager.getBoogie2Smt(), stemTF, loopTF, pref);
		} catch (TermException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			throw new AssertionError("TermException");
		}
		NonTerminationArgument nonTermArgument = lrta.checkNonTermination();
		
		List<RankingFunctionTemplate> rankingFunctionTemplates = 
				new ArrayList<RankingFunctionTemplate>();
		rankingFunctionTemplates.add(new AffineTemplate());
		rankingFunctionTemplates.add(new MultiphaseTemplate(1));
		rankingFunctionTemplates.add(new MultiphaseTemplate(2));
		rankingFunctionTemplates.add(new MultiphaseTemplate(3));
		rankingFunctionTemplates.add(new MultiphaseTemplate(4));

		RankingFunctionTemplate firstSuccessfullTemplate = null;
		for (RankingFunctionTemplate rft : rankingFunctionTemplates) {
			TerminationArgument termArg;
			try {
				termArg = lrta.tryTemplate(rft);
			} catch (SMTLIBException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
				throw new AssertionError("TermException");
			} catch (TermException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
				throw new AssertionError("TermException");
			}
			assert (nonTermArgument == null || termArg == null) : " terminating and nonterminating";
			if (termArg != null) {
				if (firstSuccessfullTemplate == null) {
					firstSuccessfullTemplate = rft;
				}
				assert termArg.getRankingFunction() != null;
				assert termArg.getSupportingInvariants() != null;
				m_Bspm.computePredicates(!withStem, termArg);
				assert m_Bspm.providesPredicates();
				assert areSupportingInvariantsCorrect() : "incorrect supporting invariant";
				assert isRankingFunctionCorrect() : "incorrect ranking function";
				m_Bspm.clearPredicates();
			}
			
		}
		TerminationArgument termArg = null;
		if (firstSuccessfullTemplate != null) {
			try {
				termArg = lrta.tryTemplate(firstSuccessfullTemplate);
			} catch (SMTLIBException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
				throw new AssertionError("TermException");
			} catch (TermException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
				throw new AssertionError("TermException");
			}
		}
		assert (nonTermArgument == null || termArg == null) : " terminating and nonterminating";
		if (termArg != null) {
			assert termArg.getRankingFunction() != null;
			assert termArg.getSupportingInvariants() != null;
			m_Bspm.computePredicates(!withStem, termArg);
			assert m_Bspm.providesPredicates();
			assert areSupportingInvariantsCorrect();
			assert isRankingFunctionCorrect();
			return SynthesisResult.TERMINATING;
		} else if (nonTermArgument != null) {
			return SynthesisResult.NONTERMINATIG;
		} else {
			return SynthesisResult.UNKNOWN;
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
