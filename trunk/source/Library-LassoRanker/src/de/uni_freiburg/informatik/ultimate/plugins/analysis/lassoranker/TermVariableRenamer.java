package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;


public class TermVariableRenamer {
	Script m_Script;
	
	public TermVariableRenamer(Script script) {
		this.m_Script = script;
	}
	
	/**
	 * Return a new transFormula where each {@code TermVariable} x_n 
	 * corresponding to {@code BoogieVar x} is replaced by a new 
	 * {@code TermVariable} named
	 * <ul>
	 * <li> prefix+In_x if x_n occurs only as inVar 
	 * <li> prefix+InOut_x if x_n occurs as inVar and outVar
	 * <li> prefix+Out_x if x_n occurs only as outVar.
	 * </ul>
	 * Otherwise x_n is not replaced.
	 */
	public TransFormula renameVars(TransFormula transFormula, String prefix) {
		Term formula = transFormula.getFormula();
		Map<BoogieVar, TermVariable> inVars = transFormula.getInVars();
		Map<BoogieVar, TermVariable> outVars = transFormula.getOutVars();
		
		Map<BoogieVar, TermVariable> newInVars = 
				new HashMap<BoogieVar, TermVariable>();
		Map<BoogieVar, TermVariable> newOutVars = 
				new HashMap<BoogieVar, TermVariable>();
		
		Collection<BoogieVar> hasInOnlyVar = new ArrayList<BoogieVar>();
		Collection<BoogieVar> hasOutOnlyVar = new ArrayList<BoogieVar>();
		Collection<BoogieVar> commonInOutVar = new ArrayList<BoogieVar>();
		
		for (BoogieVar var : inVars.keySet()) {
			TermVariable inVar = inVars.get(var);
			TermVariable outVar = outVars.get(var);
			if (inVar == outVar) {
				commonInOutVar.add(var);
			}
			else {
				hasInOnlyVar.add(var);
			}
		}
		for (BoogieVar var : outVars.keySet()) {
			TermVariable outVar = outVars.get(var);
			TermVariable inVar = inVars.get(var);
			if (inVar != outVar) {
				hasOutOnlyVar.add(var);
			}
		}
		formula = renameVars(hasInOnlyVar, formula, inVars, newInVars, prefix+"In");
		formula = renameVars(commonInOutVar, formula, inVars, newInVars, prefix+"InOut");
		formula = renameVars(commonInOutVar, formula, outVars, newOutVars, prefix+"InOut");
		formula = renameVars(hasOutOnlyVar, formula, outVars, newOutVars, prefix+"Out");
		formula = new FormulaUnLet().unlet(formula);
		return new TransFormula(formula, newInVars, newOutVars,
				transFormula.getAuxVars(), transFormula.getBranchEncoders(), 
				transFormula.isInfeasible(), transFormula.getClosedFormula());
	}
	
	/**
	 * For each {@code BoogieVar x}
	 * Let tv_old=variableMapping.get(x)
	 * <ul>
	 * <li> Create a TermVariable tv_new named prefix+x
	 * <li> replace tv_old by tv_new in formula
	 * <li> add x->tv_new to newVariableMapping
	 * <li> remove tv_old from allVars
	 * <li> add tv_new to allVars
	 * </ul>
	 */
	private Term renameVars(Collection<BoogieVar> boogieVars,
						Term formula,
						Map<BoogieVar, TermVariable> variableMapping, 
						Map<BoogieVar, TermVariable> newVariableMapping, 
						String prefix) {
		TermVariable[] vars = new TermVariable[boogieVars.size()];
		TermVariable[] newVars= new TermVariable[boogieVars.size()];
		int i=0;
		for (BoogieVar var : boogieVars) {
			vars[i] = variableMapping.get(var);
			newVars[i] = getNewTermVariable(var, vars[i], prefix);
			newVariableMapping.put(var,newVars[i]);
			i++;
		}
		try {
			formula = m_Script.let(vars, newVars, formula);
		} catch (SMTLIBException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return formula;
	}
	
	
	private TermVariable getNewTermVariable(BoogieVar var, TermVariable tv, String prefix) {
		TermVariable result = null;
		try {
			result =  m_Script.variable(prefix +"_" +var.getIdentifier(), tv.getSort());
		} catch (SMTLIBException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return result;
	}
}
