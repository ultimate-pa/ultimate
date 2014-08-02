package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.math.BigInteger;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.TreeMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.SupportingInvariant;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineSubtermNormalizer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;

public class BinaryStatePredicateManager {

	public final static String s_UnseededIdentifier = "unseeded";
	public final static String s_OldRankIdentifier = "oldRank";
	public final static int s_MaxLexComponents = 10;
	private final static boolean s_Annotate = false;

	private final Script m_Script;
	private final SmtManager m_SmtManager;
	private final BoogieNonOldVar m_UnseededVariable;
	private final BoogieNonOldVar[] m_OldRankVariables;

	/**
	 * True if predicates have been computed. False if predicates have been
	 * cleared or predicates have never been computed so far.
	 */
	private boolean m_ProvidesPredicates;

	private IPredicate m_StemPrecondition;
	private IPredicate m_StemPostcondition;
	private IPredicate m_SiConjunction;
	private IPredicate m_Honda;
	private IPredicate m_RankEqualityAndSi;
	private IPredicate m_RankEquality;
	private IPredicate m_RankDecreaseAndBound;

	private TerminationArgument m_TerminationArgument;

	private Term[] m_LexTerms;
	private IPredicate[] m_LexEquality;
	private IPredicate[] m_LexDecrease;

	/**
	 * Is the loop also terminating without the stem?
	 */
	private Boolean m_LoopTermination;
	private final Logger mLogger;
	private final IUltimateServiceProvider mServices;

	public BinaryStatePredicateManager(SmtManager smtManager, IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		m_Script = smtManager.getScript();
		m_SmtManager = smtManager;
		Boogie2SMT boogie2Smt = smtManager.getBoogie2Smt();
		m_UnseededVariable = constructGlobalBoogieVar(s_UnseededIdentifier, boogie2Smt, BoogieType.boolType);

		m_OldRankVariables = new BoogieNonOldVar[s_MaxLexComponents];
		for (int i = 0; i < s_MaxLexComponents; i++) {
			String name = s_OldRankIdentifier + i;
			m_OldRankVariables[i] = constructGlobalBoogieVar(name, boogie2Smt, BoogieType.intType);
		}
	}

	/**
	 * Construct a global BoogieVar and the corresponding oldVar. Return the
	 * global var.
	 * 
	 * @param type
	 */
	private BoogieNonOldVar constructGlobalBoogieVar(String name, Boogie2SMT boogie2Smt, PrimitiveType type) {
		BoogieNonOldVar globalBv = boogie2Smt.constructAuxiliaryGlobalBoogieVar(name, null, type, null);
		return globalBv;
	}

	public boolean providesPredicates() {
		return m_ProvidesPredicates;
	}

	public boolean isLoopWithoutStemTerminating() {
		assert m_ProvidesPredicates;
		return m_LoopTermination;
	}

	public TerminationArgument getTerminationArgument() {
		assert m_ProvidesPredicates;
		return m_TerminationArgument;
	}

	/**
	 * Compute IPredicate that states that the current value of the ranking
	 * function f is smaller than or equal to the value of oldrank. I.e.,
	 * (f_0,...f_n) <=_lex (oldrk_0,...,oldrk_n)
	 */
	public IPredicate getRankEquality() {
		return m_RankEquality;
	}

	/**
	 * Compute IPredicate that states that the current value of the ranking
	 * function f is strictly smaller than the value of oldrank and bounded from
	 * below. We use a formula similar to (f_0,...f_n) <_lex
	 * (oldrk_0,...,oldrk_n) with the additional constraint that for the
	 * decreasing component oldrk_i>=0 holds.
	 */
	public IPredicate getRankDecreaseAndBound() {
		return m_RankDecreaseAndBound;
	}

	public IPredicate getStemPrecondition() {
		assert m_ProvidesPredicates;
		return m_StemPrecondition;
	}

	public IPredicate getStemPostcondition() {
		assert m_ProvidesPredicates;
		return m_StemPostcondition;
	}

	public IPredicate getSiConjunction() {
		assert m_ProvidesPredicates;
		return m_SiConjunction;
	}

	@Deprecated
	public IPredicate getHondaPredicate() {
		assert m_ProvidesPredicates;
		return m_Honda;
	}

	@Deprecated
	public IPredicate getRankEqAndSi() {
		assert m_ProvidesPredicates;
		return m_RankEqualityAndSi;
	}

	public BoogieNonOldVar getUnseededVariable() {
		assert m_ProvidesPredicates;
		return m_UnseededVariable;
	}

	public BoogieNonOldVar[] getOldRankVariables() {
		assert m_ProvidesPredicates;
		return m_OldRankVariables;
	}

	public void clearPredicates() {
		if (!m_ProvidesPredicates) {
			throw new AssertionError("no predicates provided cannot clear");
		}
		m_LoopTermination = null;
		m_TerminationArgument = null;
		m_StemPrecondition = null;
		m_StemPostcondition = null;
		m_SiConjunction = null;
		m_Honda = null;
		m_RankEqualityAndSi = null;
		m_RankEquality = null;
		m_RankDecreaseAndBound = null;
		m_ProvidesPredicates = false;
		m_LexDecrease = null;
		m_LexEquality = null;
		m_LexTerms = null;
	}

	public void computePredicates(boolean loopTermination, TerminationArgument termArg) {
		assert m_LoopTermination == null;
		assert m_TerminationArgument == null;
		assert m_StemPrecondition == null;
		assert m_StemPostcondition == null;
		assert m_Honda == null;
		assert m_RankEqualityAndSi == null;
		assert m_RankEquality == null;
		assert m_RankDecreaseAndBound == null;
		assert m_LexDecrease == null;
		assert m_LexEquality == null;
		assert m_LexTerms == null;
		m_LoopTermination = loopTermination;
		m_TerminationArgument = termArg;
		IPredicate unseededPredicate = unseededPredicate();
		m_StemPrecondition = unseededPredicate;
		m_SiConjunction = computeSiConjunction(m_TerminationArgument.getSupportingInvariants(),
				m_TerminationArgument.getArrayIndexSupportingInvariants());
		boolean siConjunctionIsTrue = isTrue(m_SiConjunction);
		if (siConjunctionIsTrue) {
			m_StemPostcondition = unseededPredicate;
		} else {
			TermVarsProc tvp = m_SmtManager.and(unseededPredicate, m_SiConjunction);
			m_StemPostcondition = m_SmtManager.newPredicate(tvp.getFormula(), tvp.getProcedures(), tvp.getVars(),
					tvp.getClosedFormula());
		}
		RankingFunction rf = m_TerminationArgument.getRankingFunction();
		decodeLex(rf);
		m_RankEquality = computeRankEquality();
		if (siConjunctionIsTrue) {
			m_RankEqualityAndSi = m_RankEquality;
		} else {
			TermVarsProc tvp = m_SmtManager.and(m_RankEquality, m_SiConjunction);
			m_RankEqualityAndSi = m_SmtManager.newPredicate(tvp.getFormula(), tvp.getProcedures(), tvp.getVars(),
					tvp.getClosedFormula());
		}
		m_RankDecreaseAndBound = computeRankDecreaseAndBound();
		IPredicate unseededOrRankDecrease;
		{
			TermVarsProc tvp = m_SmtManager.or(unseededPredicate, m_RankDecreaseAndBound);
			unseededOrRankDecrease = m_SmtManager.newPredicate(tvp.getFormula(), tvp.getProcedures(), tvp.getVars(),
					tvp.getClosedFormula());
		}
		if (siConjunctionIsTrue) {
			m_Honda = unseededOrRankDecrease;
		} else {
			TermVarsProc tvp = m_SmtManager.and(m_SiConjunction, unseededOrRankDecrease);
			m_Honda = m_SmtManager.newPredicate(tvp.getFormula(), tvp.getProcedures(), tvp.getVars(),
					tvp.getClosedFormula());
		}
		m_ProvidesPredicates = true;
	}

	private IPredicate unseededPredicate() {
		Set<BoogieVar> vars = new HashSet<BoogieVar>(1);
		vars.add(m_UnseededVariable);
		Term formula = m_UnseededVariable.getTermVariable();
		IPredicate result = m_SmtManager.newPredicate(formula, new String[0], vars,
				m_UnseededVariable.getDefaultConstant());
		return result;
	}

	private IPredicate computeSiConjunction(Collection<SupportingInvariant> siList, Collection<Term> aisi) {
		Term[] siTerms = new Term[siList.size() + aisi.size()];
		int i = 0;
		for (SupportingInvariant si : siList) {
			Term formula = si.asTerm(m_SmtManager.getScript());
			siTerms[i] = formula;
			i++;
		}
		assert i == siList.size();
		int j = 0;
		for (Term term : aisi) {
			siTerms[i + j] = term;
			j++;
		}
		Term conjunction = Util.and(m_Script, siTerms);
		Term simplified = m_SmtManager.simplify(conjunction);
		Term normalized = (new AffineSubtermNormalizer(m_SmtManager.getScript(), mLogger)).transform(simplified);
		TermVarsProc tvp = TermVarsProc.computeTermVarsProc(normalized, m_SmtManager.getBoogie2Smt());
		return m_SmtManager.newPredicate(tvp);
	}

	public IPredicate supportingInvariant2Predicate(SupportingInvariant si) {
		Term formula = si.asTerm(m_SmtManager.getScript());
		formula = m_SmtManager.simplify(formula);
		return term2Predicate(formula);
	}

	public IPredicate term2Predicate(Term term) {
		TermVarsProc termVarsProc = TermVarsProc.computeTermVarsProc(term, m_SmtManager.getBoogie2Smt());
		IPredicate result = m_SmtManager.newPredicate(termVarsProc);
		return result;
	}

	/**
	 * Given a RankingFunction with lex terms (f_0, ..., f_n), initialize the
	 * array m_LexEquality with the terms (oldrank_0 >= f_0, ..., oldrank_n >=
	 * f_n) and initialize the array m_LexDecrease with the terms (oldrank_0 >
	 * f_0 &&, ..., oldrank_n > f_n).
	 */
	private void decodeLex(RankingFunction rf) {
		m_LexTerms = rf.asLexTerm(m_Script);
		m_LexEquality = new IPredicate[m_LexTerms.length];
		for (int i = 0; i < m_LexTerms.length; i++) {
			m_LexEquality[i] = getRankInEquality(m_LexTerms[i], ">=", m_OldRankVariables[i], false);
			if (s_Annotate) {
				String name = "equality" + i;
				Annotation annot = new Annotation(":named", name);
				m_LexTerms[i] = m_Script.annotate(m_LexTerms[i], annot);
			}
		}
		m_LexDecrease = new IPredicate[m_LexTerms.length];
		for (int i = 0; i < m_LexTerms.length; i++) {
			m_LexDecrease[i] = getRankInEquality(m_LexTerms[i], ">", m_OldRankVariables[i], true);
			if (s_Annotate) {
				String name = "strictDecrease" + i;
				Annotation annot = new Annotation(":named", name);
				m_LexTerms[i] = m_Script.annotate(m_LexTerms[i], annot);
			}
		}
	}

	private IPredicate computeRankEquality() {
		TermVarsProc tvp = m_SmtManager.and(m_LexEquality);
		IPredicate result = m_SmtManager.newPredicate(tvp.getFormula(), tvp.getProcedures(), tvp.getVars(),
				tvp.getClosedFormula());
		return result;
	}

	private IPredicate computeRankDecreaseAndBound() {
		IPredicate[] disjuncts = new IPredicate[m_LexTerms.length];
		for (int i = 0; i < m_LexTerms.length; i++) {
			IPredicate[] conjuncts = new IPredicate[i + 1];
			for (int j = 0; j < i; j++) {
				conjuncts[j] = m_LexEquality[j];
			}
			conjuncts[i] = m_LexDecrease[i];
			TermVarsProc tvp = m_SmtManager.and(conjuncts);
			disjuncts[i] = m_SmtManager.newPredicate(tvp);
		}

		TermVarsProc tvp = m_SmtManager.or(disjuncts);
		IPredicate result = m_SmtManager.newPredicate(tvp);
		return result;
	}

	private IPredicate getRankInEquality(Term rfTerm, String symbol, BoogieVar oldRankVariable, boolean addGeq0) {
		assert symbol.equals(">=") || symbol.equals(">");
		TermVarsProc termVarsProc = TermVarsProc.computeTermVarsProc(rfTerm, m_SmtManager.getBoogie2Smt());

		Term equality = m_Script.term(symbol, oldRankVariable.getTermVariable(), rfTerm);
		if (addGeq0) {
			equality = Util.and(m_Script, equality, getRankGeq0(oldRankVariable));
		}

		Set<BoogieVar> vars = new HashSet<BoogieVar>();
		vars.add(oldRankVariable);
		vars.addAll(termVarsProc.getVars());

		Term closedFormula = PredicateUtils.computeClosedFormula(equality, vars, m_Script);

		IPredicate result = m_SmtManager.newPredicate(equality, termVarsProc.getProcedures(), vars, closedFormula);
		return result;
	}

	private Term getRankGeq0(BoogieVar oldRankVariable) {
		Term geq = m_Script.term(">=", oldRankVariable.getTermVariable(), m_Script.numeral(BigInteger.ZERO));
		return geq;
	}

	public boolean checkSupportingInvariant(IPredicate siPredicate, NestedWord<CodeBlock> stem,
			NestedWord<CodeBlock> loop, ModifiableGlobalVariableManager modGlobVarManager) {
		boolean result = true;
		TraceChecker traceChecker;
		IPredicate truePredicate = m_SmtManager.newTruePredicate();
		if (isTrue(siPredicate)) {
			siPredicate = truePredicate;
		}
		traceChecker = new TraceChecker(truePredicate, siPredicate, new TreeMap<Integer, IPredicate>(), stem,
				m_SmtManager, modGlobVarManager, /*
												 * TODO: When Matthias
												 * introduced this parameter he
												 * set the argument to false.
												 * Check if you want to set this
												 * to true.
												 */false, mServices);
		LBool stemCheck = traceChecker.isCorrect();
		if (stemCheck == LBool.UNSAT) {
			traceChecker.finishTraceCheckWithoutInterpolantsOrProgramExecution();
			// IPredicate[] interpolants = m_TraceChecker.getInterpolants(new
			// TraceChecker.AllIntegers());
			// interpolants.toString();
		} else {
			traceChecker.finishTraceCheckWithoutInterpolantsOrProgramExecution();
			result = false;
		}
		traceChecker = new TraceChecker(siPredicate, siPredicate, new TreeMap<Integer, IPredicate>(), stem,
				m_SmtManager, modGlobVarManager, /*
												 * TODO: When Matthias
												 * introduced this parameter he
												 * set the argument to false.
												 * Check if you want to set this
												 * to true.
												 */false, mServices);
		LBool loopCheck = traceChecker.isCorrect();
		if (loopCheck == LBool.UNSAT) {
			traceChecker.finishTraceCheckWithoutInterpolantsOrProgramExecution();
			// IPredicate[] interpolants = m_TraceChecker.getInterpolants(new
			// TraceChecker.AllIntegers());
			// interpolants.toString();
		} else {
			traceChecker.finishTraceCheckWithoutInterpolantsOrProgramExecution();
			result = false;
		}
		return result;
	}

	public boolean checkRankDecrease(NestedWord<CodeBlock> loop, ModifiableGlobalVariableManager modGlobVarManager) {
		TraceChecker traceChecker = new TraceChecker(m_RankEqualityAndSi, m_RankDecreaseAndBound,
				new TreeMap<Integer, IPredicate>(), loop, m_SmtManager, modGlobVarManager,
				/*
				 * TODO : When Matthias introduced this parameter he set the
				 * argument to false . Check if you want to set this to true .
				 */false, mServices);
		LBool loopCheck = traceChecker.isCorrect();
		traceChecker.finishTraceCheckWithoutInterpolantsOrProgramExecution();
		return (loopCheck == LBool.UNSAT);
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

	public boolean containsOldRankVariable(IPredicate pred) {
		for (BoogieVar rankVariable : getOldRankVariables()) {
			if (pred.getVars().contains(rankVariable)) {
				return true;
			}
		}
		return false;
	}

}
