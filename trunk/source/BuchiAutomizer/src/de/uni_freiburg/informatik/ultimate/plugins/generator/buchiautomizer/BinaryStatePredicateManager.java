package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.SupportingInvariant;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.functions.LinearRankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.functions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;

public class BinaryStatePredicateManager {
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	public final static String s_SeedSuffix = "_seed";
	
	private final Script m_Script;
	private final SmtManager m_SmtManager;
	private final BoogieVar m_OldRankVariable;
	private final BoogieVar m_UnseededVariable;
	
	private IPredicate m_StemPrecondition;
	private IPredicate m_StemPostcondition;
	private IPredicate m_HondaPredicate;
	private IPredicate m_RankDecreaseAndSi;

	private IPredicate m_RankDecrease;
	
	public BinaryStatePredicateManager(SmtManager smtManager) {
		m_Script = smtManager.getScript();
		m_SmtManager = smtManager;
		m_OldRankVariable = constructOldRankVariable();
		m_UnseededVariable = constructUnseededVariable();
	}
	
	public IPredicate getStemPrecondition() {
		return m_StemPrecondition;
	}

	public IPredicate getStemPostcondition() {
		return m_StemPostcondition;
	}

	public IPredicate getHondaPredicate() {
		return m_HondaPredicate;
	}

	public IPredicate getRankDecreaseAndSi() {
		return m_RankDecreaseAndSi;
	}
	
	public BoogieVar getUnseededVariable() {
		return m_UnseededVariable;
	}
	
	public BoogieVar getOldRankVariable() {
		return m_OldRankVariable;
	}

	public void computePredicates(LinearRankingFunction rf, Iterable<SupportingInvariant> siList) {
		IPredicate unseededPredicate = unseededPredicate();
		m_StemPrecondition = unseededPredicate;
		IPredicate siConjunction = computeSiConjunction(siList);
		boolean siConjunctionIsTrue = isTrue(siConjunction);
		if (siConjunctionIsTrue) {
			m_StemPostcondition = unseededPredicate;
		} else {
			TermVarsProc tvp = m_SmtManager.and(unseededPredicate, siConjunction);
			m_StemPostcondition = m_SmtManager.newPredicate(tvp.getFormula(), 
					tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula()); 
		}
		IPredicate rankEquality = getRankEquality(rf);
		if (siConjunctionIsTrue) {
			m_HondaPredicate = rankEquality;
		} else {
			TermVarsProc tvp = m_SmtManager.and(rankEquality, siConjunction);
			m_HondaPredicate = m_SmtManager.newPredicate(tvp.getFormula(), 
					tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula()); 
		}
		m_RankDecrease = getRankDecrease(rf);
		IPredicate unseededOrRankDecrease; 
		{
			TermVarsProc tvp = m_SmtManager.or(unseededPredicate, m_RankDecrease);
			unseededOrRankDecrease = m_SmtManager.newPredicate(tvp.getFormula(), 
					tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
		}
		if (siConjunctionIsTrue) {
			m_RankDecreaseAndSi = unseededOrRankDecrease;
		} else {
			TermVarsProc tvp = m_SmtManager.and(siConjunction, unseededOrRankDecrease);
			m_RankDecreaseAndSi = m_SmtManager.newPredicate(tvp.getFormula(), 
					tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
		}

	}


	private BoogieVar constructOldRankVariable() {
		Sort sort = m_Script.sort("Int");
		String name = "oldRank";
		TermVariable termVariable = m_Script.variable(name, sort);
		
		ApplicationTerm defaultConstant;
		{
			String defaultConstantName = "c_" + name;
			m_Script.declareFun(defaultConstantName, new Sort[0], sort);
			defaultConstant = (ApplicationTerm) m_Script.term(defaultConstantName);
		}
		ApplicationTerm primedConstant;
		{
			String primedConstantName = "c_" + name + "_primed";
			m_Script.declareFun(primedConstantName, new Sort[0], sort);
			primedConstant = (ApplicationTerm) m_Script.term(primedConstantName);
		}
		BoogieVar oldRank = new BoogieVar(name,
				null, BoogieType.intType, false, 
				termVariable, defaultConstant, primedConstant);
		return oldRank;
	}
	
	private BoogieVar constructUnseededVariable() {
		Sort sort = m_Script.sort("Bool");
		String name = "unseeded";
		TermVariable termVariable = m_Script.variable(name, sort);
		
		ApplicationTerm defaultConstant;
		{
			String defaultConstantName = "c_" + name;
			m_Script.declareFun(defaultConstantName, new Sort[0], sort);
			defaultConstant = (ApplicationTerm) m_Script.term(defaultConstantName);
		}
		ApplicationTerm primedConstant;
		{
			String primedConstantName = "c_" + name + "_primed";
			m_Script.declareFun(primedConstantName, new Sort[0], sort);
			primedConstant = (ApplicationTerm) m_Script.term(primedConstantName);
		}
		BoogieVar oldRank = new BoogieVar(name,
				null, BoogieType.boolType, false, 
				termVariable, defaultConstant, primedConstant);
		return oldRank;
	}

	
	private IPredicate unseededPredicate() {
		Set<BoogieVar> vars = new HashSet<BoogieVar>(1);
		vars.add(m_UnseededVariable);
		Term formula = m_UnseededVariable.getTermVariable();
		IPredicate result = m_SmtManager.newPredicate(formula, 
				new String[0], vars,m_UnseededVariable.getDefaultConstant());
		return result;
	}
	
	private IPredicate computeSiConjunction(Iterable<SupportingInvariant> siList) {
		List<IPredicate> siPreds = new ArrayList<IPredicate>();
		for (SupportingInvariant si : siList) {
			IPredicate siPred = supportingInvariant2Predicate(si);
			siPreds.add(siPred);
		}
		TermVarsProc tvp = m_SmtManager.and(siPreds.toArray(new IPredicate[0]));
		IPredicate siConjunction = m_SmtManager.newPredicate(tvp.getFormula(), 
				tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula()); 
		return siConjunction;
	}
	
	
	private IPredicate supportingInvariant2Predicate(SupportingInvariant si) {
		Set<BoogieVar> coefficients = si.getCoefficients().keySet();
		Term formula = si.asTerm(m_SmtManager.getScript(), m_SmtManager.getBoogieVar2SmtVar());
		formula = (new SimplifyDDA(m_Script, s_Logger)).getSimplifiedTerm(formula);
		TermVarsProc termVarsProc = m_SmtManager.computeTermVarsProc(formula);
		assert termVarsProc.getVars().equals(coefficients);
		
		IPredicate result = m_SmtManager.newPredicate(termVarsProc.getFormula(),
				termVarsProc.getProcedures(), termVarsProc.getVars(), termVarsProc.getClosedFormula());
		return result;
	}
	
	private IPredicate getRankEquality(RankingFunction rf) {
		return getRankInEquality(rf, "=");
	}
	
	private IPredicate getRankDecrease(RankingFunction rf) {
		return getRankInEquality(rf, ">");
	}

	
	
	private IPredicate getRankInEquality(RankingFunction rf, String symbol) {
		assert symbol.equals("=") || symbol.equals(">");
		Term rfTerm = rf.asFormula(m_Script, m_SmtManager.getBoogieVar2SmtVar());
		TermVarsProc termVarsProc = m_SmtManager.computeTermVarsProc(rfTerm);
		
		Term equality = m_Script.term(symbol, m_OldRankVariable.getTermVariable(), rfTerm);
		
		Set<BoogieVar> vars = new HashSet<BoogieVar>();
		vars.add(m_OldRankVariable);
		vars.addAll(termVarsProc.getVars());
		
		Term closedFormula = SmtManager.computeClosedFormula(equality, vars, m_Script);
		
		IPredicate result = m_SmtManager.newPredicate(equality,
				termVarsProc.getProcedures(), vars, closedFormula);
		return result;
	}
	
	
	
	public boolean checkSupportingInvariant(SupportingInvariant si, 
			NestedWord<CodeBlock> stem, NestedWord<CodeBlock> loop, 
			RootAnnot rootAnnot) {
		boolean result = true;
		TraceChecker traceChecker = new TraceChecker(m_SmtManager,
				rootAnnot.getModifiedVars(),
				rootAnnot.getEntryNodes(),
				null);
		IPredicate truePredicate = m_SmtManager.newTruePredicate();
		IPredicate siPred = supportingInvariant2Predicate(si);
		if (isTrue(siPred)) {
			siPred = truePredicate;
		}
		LBool stemCheck = traceChecker.checkTrace(truePredicate, siPred, stem);
		if (stemCheck == LBool.UNSAT) {
			traceChecker.forgetTrace();
//			IPredicate[] interpolants = m_TraceChecker.getInterpolants(new TraceChecker.AllIntegers());
//			interpolants.toString();
		} else {
			result = false;			
		}
		LBool loopCheck = traceChecker.checkTrace(siPred, siPred, stem);
		if (loopCheck == LBool.UNSAT) {
			traceChecker.forgetTrace();
//			IPredicate[] interpolants = m_TraceChecker.getInterpolants(new TraceChecker.AllIntegers());
//			interpolants.toString();
		} else {
			result = false;
		}
		return result;
	}
	
	public boolean checkRankDecrease(NestedWord<CodeBlock> loop, RootAnnot rootAnnot) {
		TraceChecker traceChecker = new TraceChecker(m_SmtManager,
				rootAnnot.getModifiedVars(),
				rootAnnot.getEntryNodes(),
				null);
		LBool loopCheck = traceChecker.checkTrace(m_HondaPredicate, m_RankDecrease, loop);
		traceChecker.forgetTrace();
		if (loopCheck == LBool.UNSAT) {
			return true;
		} else {
			return false;
		}
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

}
