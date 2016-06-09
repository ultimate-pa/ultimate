/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LassoRanker plug-in.
 * 
 * The ULTIMATE LassoRanker plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LassoRanker plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LassoRanker plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;


/**
 * @author Matthias Heizmann
 */
public class TermVariableRenamer {
	private final Script mScript;
	
	public TermVariableRenamer(Script script) {
		mScript = script;
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
		final Map<BoogieVar, TermVariable> inVars = transFormula.getInVars();
		final Map<BoogieVar, TermVariable> outVars = transFormula.getOutVars();
		
		final Map<BoogieVar, TermVariable> newInVars = 
				new LinkedHashMap<BoogieVar, TermVariable>();
		final Map<BoogieVar, TermVariable> newOutVars = 
				new LinkedHashMap<BoogieVar, TermVariable>();
		
		final Collection<BoogieVar> hasInOnlyVar = new ArrayList<BoogieVar>();
		final Collection<BoogieVar> hasOutOnlyVar = new ArrayList<BoogieVar>();
		final Collection<BoogieVar> commonInOutVar = new ArrayList<BoogieVar>();
		
		for (final BoogieVar var : inVars.keySet()) {
			final TermVariable inVar = inVars.get(var);
			final TermVariable outVar = outVars.get(var);
			if (inVar == outVar) {
				commonInOutVar.add(var);
			}
			else {
				hasInOnlyVar.add(var);
			}
		}
		for (final BoogieVar var : outVars.keySet()) {
			final TermVariable outVar = outVars.get(var);
			final TermVariable inVar = inVars.get(var);
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
		final TermVariable[] vars = new TermVariable[boogieVars.size()];
		final TermVariable[] newVars= new TermVariable[boogieVars.size()];
		int i=0;
		for (final BoogieVar var : boogieVars) {
			vars[i] = variableMapping.get(var);
			newVars[i] = getNewTermVariable(var, vars[i], prefix);
			newVariableMapping.put(var,newVars[i]);
			i++;
		}
		try {
			formula = mScript.let(vars, newVars, formula);
		} catch (final SMTLIBException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return formula;
	}
	
	
	private TermVariable getNewTermVariable(BoogieVar var, TermVariable tv, String prefix) {
		TermVariable result = null;
		try {
			result =  mScript.variable(prefix +"_" +var.getIdentifier(), tv.getSort());
		} catch (final SMTLIBException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return result;
	}
}
