package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.SupportingInvariant;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.functions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager.TermVarsProc;

public class BinaryStatePredicateManager {
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	public final static String s_SeedSuffix = "_seed";
	
	private final Script m_Script;
	private final SmtManager m_SmtManager;
	private final Map<BoogieVar,BoogieVar> m_BoogieVar2SeededBoogieVar;
	
	
	public BinaryStatePredicateManager(SmtManager smtManager) {
		m_Script = smtManager.getScript();
		m_SmtManager = smtManager;
		m_BoogieVar2SeededBoogieVar = new HashMap<BoogieVar,BoogieVar>();
	}
	
	public IPredicate supportingInvariant2Predicate(SupportingInvariant si) {
		Set<BoogieVar> coefficients = si.getCoefficients().keySet();
		Term formula = si.asTerm(m_SmtManager.getScript(), m_SmtManager.getBoogieVar2SmtVar());
		formula = (new SimplifyDDA(m_Script, s_Logger)).getSimplifiedTerm(formula);
		TermVarsProc termVarsProc = m_SmtManager.computeTermVarsProc(formula);
		assert termVarsProc.getVars().equals(coefficients);
		
		IPredicate result = m_SmtManager.newPredicate(termVarsProc.getFormula(),
				termVarsProc.getProcedures(), termVarsProc.getVars(), termVarsProc.getClosedFormula());
		return result;
	}
	
	
	public IPredicate getSeedVarEquality(RankingFunction rf) {
		Term unseededTerm = rf.asFormula(m_Script, m_SmtManager.getBoogieVar2SmtVar());
		TermVarsProc termVarsProc = m_SmtManager.computeTermVarsProc(unseededTerm);
		
		List<Term> equalities = new ArrayList<Term>();
		Set<BoogieVar> seededBoogieVars = new HashSet<BoogieVar>();
		
		for (BoogieVar bv : termVarsProc.getVars()) {
			BoogieVar seededBv = getSeedVariable(bv);
			seededBoogieVars.add(seededBv);
			Term equality = m_Script.term("=", bv.getTermVariable(), seededBv.getTermVariable());
			equalities.add(equality);
		}
		Term equality = Util.and(m_Script, equalities.toArray(new Term[0]));
		
//		assert equals(obj)
//		Term equality;
//		if (equalities.size() == 1) {
//			equality = equalities.get(0);
//		} else {
//			equality = m_Script.term("and", equalities.toArray(new Term[0]));
//		}
		
		Set<BoogieVar> seededAndUnseeded = new HashSet<BoogieVar>();
		seededAndUnseeded.addAll(seededBoogieVars);
		seededAndUnseeded.addAll(termVarsProc.getVars());
		
		Term closedFormula = SmtManager.computeClosedFormula(equality, seededAndUnseeded, m_Script);
		
		IPredicate result = m_SmtManager.newPredicate(equality,
				termVarsProc.getProcedures(), seededAndUnseeded, closedFormula);
		return result;
	}
	

	public IPredicate getRankDecrease(RankingFunction rf) {
		Term unseededTerm = rf.asFormula(m_Script, m_SmtManager.getBoogieVar2SmtVar());
		TermVarsProc termVarsProc = m_SmtManager.computeTermVarsProc(unseededTerm);
		
		Set<BoogieVar> seededBoogieVars = new HashSet<BoogieVar>();
		
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();
		for (BoogieVar bv : termVarsProc.getVars()) {
			BoogieVar seededBv = getSeedVariable(bv);
			seededBoogieVars.add(seededBv);
			replacees.add(bv.getTermVariable());
			replacers.add(seededBv.getTermVariable());
		}
		TermVariable[] substVars = replacees.toArray(new TermVariable[replacees.size()]);
		Term[] substValues = replacers.toArray(new Term[replacers.size()]);
		Term seededTerm = m_Script.let(substVars , substValues, unseededTerm);
		seededTerm = (new FormulaUnLet()).unlet(seededTerm);
		
		Set<BoogieVar> seededAndUnseeded = new HashSet<BoogieVar>();
		seededAndUnseeded.addAll(seededBoogieVars);
		seededAndUnseeded.addAll(termVarsProc.getVars());
		
		Term formula = m_Script.term("<", unseededTerm, seededTerm);
		Term closedFormula = SmtManager.computeClosedFormula(formula, seededAndUnseeded, m_Script);
		
		IPredicate result = m_SmtManager.newPredicate(formula,
				termVarsProc.getProcedures(), seededAndUnseeded, closedFormula);
		return result;
	}

	
	
	public BoogieVar getSeedVariable(BoogieVar bv) {
		if (m_BoogieVar2SeededBoogieVar.containsKey(bv)) {
			return m_BoogieVar2SeededBoogieVar.get(bv);
		} else {
			Sort sort = bv.getTermVariable().getSort();
			String name = bv.getGloballyUniqueId() + s_SeedSuffix;
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
			BoogieVar seeded = new BoogieVar(name,
					null, bv.getIType(), bv.isOldvar(), 
					termVariable, defaultConstant, primedConstant);
			m_BoogieVar2SeededBoogieVar.put(bv, seeded);
			return seeded;
		}
	}
	

}
