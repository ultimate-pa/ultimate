/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieOldVar;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula.Infeasibility;

public class BuchiModGlobalVarManager extends ModifiableGlobalVariableManager {
	private final BoogieNonOldVar m_Unseeded;
	private final BoogieNonOldVar[] m_OldRank;
	private final BoogieOldVar m_UnseededOldVar;
	private final BoogieOldVar[] m_OldRankOldVar;
	private final Boogie2SMT m_Boogie2smt;
	private final Script m_Script;
	
	private final Map<String, TransFormula> m_Proc2OldVarsAssignment;
	private final Map<String, TransFormula> m_Proc2GlobalVarsAssignment;

	public BuchiModGlobalVarManager(BoogieNonOldVar unseeded, BoogieNonOldVar[] oldRank,
			ModifiableGlobalVariableManager modifiableGlobalVariableManager, 
			Boogie2SMT boogie2Smt) {
		super(modifiableGlobalVariableManager);
		m_Boogie2smt = boogie2Smt;
		m_Unseeded = unseeded;
		m_UnseededOldVar = unseeded.getOldVar();
		assert m_UnseededOldVar != null : "oldVar missing";
		m_OldRank = oldRank;
		m_OldRankOldVar = new BoogieOldVar[oldRank.length];
		for (int i=0; i<oldRank.length; i++) {
			m_OldRankOldVar[i] = oldRank[i].getOldVar();
			assert m_OldRankOldVar[i] != null : "oldVar missing";
		}
		m_Script  = boogie2Smt.getScript();
		m_Proc2OldVarsAssignment = new HashMap<String, TransFormula>();
		m_Proc2GlobalVarsAssignment = new HashMap<String, TransFormula>();
	}

	
	@Override
	public TransFormula getOldVarsAssignment(String proc) {
		TransFormula oldVarsAssignment = m_Proc2OldVarsAssignment.get(proc);
		if (oldVarsAssignment == null) {
			oldVarsAssignment = constructOldVarsAssignment(proc);
			m_Proc2OldVarsAssignment.put(proc, oldVarsAssignment);
		}
		return m_Proc2OldVarsAssignment.get(proc);
	}
	
	

	@Override
	public TransFormula getGlobalVarsAssignment(String proc) {
		TransFormula globalVarsAssignment = m_Proc2GlobalVarsAssignment.get(proc);
		if (globalVarsAssignment == null) {
			globalVarsAssignment = constructGlobalVarsAssignment(proc);
			m_Proc2GlobalVarsAssignment.put(proc, globalVarsAssignment);
		}
		return m_Proc2GlobalVarsAssignment.get(proc);
	}
	
	
	private TransFormula constructOldVarsAssignment(String proc) {
		TransFormula without = super.getOldVarsAssignment(proc);
		
		Term formula = without.getFormula();
		Map<BoogieVar, TermVariable> inVars = 
				new HashMap<BoogieVar, TermVariable>(without.getInVars());
		Map<BoogieVar, TermVariable> outVars = 
				new HashMap<BoogieVar, TermVariable>(without.getOutVars());
		Set<TermVariable> auxVars = without.getAuxVars();
		Set<TermVariable> branchEncoders = without.getBranchEncoders();
		assert branchEncoders.isEmpty();
		Infeasibility infeasibility = without.isInfeasible();
		assert infeasibility == Infeasibility.UNPROVEABLE;
		formula = Util.and(m_Script, formula, oldVarEquality(m_Unseeded, m_UnseededOldVar));
		inVars.put(m_Unseeded, m_Unseeded.getTermVariable());
		outVars.put(m_Unseeded, m_Unseeded.getTermVariable());
		outVars.put(m_UnseededOldVar, m_UnseededOldVar.getTermVariable());
		for (int i=0; i<m_OldRank.length; i++) {
			formula = Util.and(m_Script, formula, oldVarEquality(m_OldRank[i], m_OldRankOldVar[i]));
			inVars.put(m_OldRank[i], m_OldRank[i].getTermVariable());
			outVars.put(m_OldRank[i], m_OldRank[i].getTermVariable());
			outVars.put(m_OldRankOldVar[i], m_OldRankOldVar[i].getTermVariable());
		}
		Term closedFormula = TransFormula.computeClosedFormula(
				formula, inVars, outVars, auxVars, false, m_Boogie2smt);
		TransFormula result = new TransFormula(formula, inVars, outVars, 
				auxVars, branchEncoders, infeasibility, closedFormula);
		return result;
	}
	
	
	private TransFormula constructGlobalVarsAssignment(String proc) {
		TransFormula without = super.getGlobalVarsAssignment(proc);
		
		Term formula = without.getFormula();
		Map<BoogieVar, TermVariable> inVars = 
				new HashMap<BoogieVar, TermVariable>(without.getInVars());
		Map<BoogieVar, TermVariable> outVars = 
				new HashMap<BoogieVar, TermVariable>(without.getOutVars());
		Set<TermVariable> auxVars = without.getAuxVars();
		Set<TermVariable> branchEncoders = without.getBranchEncoders();
		assert branchEncoders.isEmpty();
		Infeasibility infeasibility = without.isInfeasible();
		assert infeasibility == Infeasibility.UNPROVEABLE;
		formula = Util.and(m_Script, formula, oldVarEquality(m_Unseeded, m_UnseededOldVar));
		inVars.put(m_UnseededOldVar, m_UnseededOldVar.getTermVariable());
		outVars.put(m_UnseededOldVar, m_UnseededOldVar.getTermVariable());
		outVars.put(m_Unseeded, m_Unseeded.getTermVariable());
		for (int i=0; i<m_OldRank.length; i++) {
			formula = Util.and(m_Script, formula, oldVarEquality(m_OldRank[i], m_OldRankOldVar[i]));
			inVars.put(m_OldRankOldVar[i], m_OldRankOldVar[i].getTermVariable());
			outVars.put(m_OldRankOldVar[i], m_OldRankOldVar[i].getTermVariable());
			outVars.put(m_OldRank[i], m_OldRank[i].getTermVariable());
		}
		Term closedFormula = TransFormula.computeClosedFormula(
				formula, inVars, outVars, auxVars, false, m_Boogie2smt);
		TransFormula result = new TransFormula(formula, inVars, outVars, 
				auxVars, branchEncoders, infeasibility, closedFormula);
		return result;
	}


	
	public Term oldVarEquality(BoogieVar var, BoogieVar oldVar) {
		return m_Script.term("=", var.getTermVariable(), oldVar.getTermVariable());
	}


	@Override
	public Map<String, BoogieNonOldVar> getGlobals() {
		HashMap<String, BoogieNonOldVar> result = 
				new HashMap<String, BoogieNonOldVar>(super.getGlobals());
		for (int i=0; i<m_OldRank.length; i++) {
			result.put(m_OldRank[i].getIdentifier(),m_OldRank[i]);
		}
		result.put(m_Unseeded.getIdentifier(),m_Unseeded);
		return result;
	}

}
