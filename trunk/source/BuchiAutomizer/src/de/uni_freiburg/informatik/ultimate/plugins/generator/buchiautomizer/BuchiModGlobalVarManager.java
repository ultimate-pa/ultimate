package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula.Infeasibility;

public class BuchiModGlobalVarManager extends ModifiableGlobalVariableManager {
	private final BoogieVar m_Unseeded;
	private final BoogieVar[] m_OldRank;
	private final BoogieVar m_UnseededOldVar;
	private final BoogieVar[] m_OldRankOldVar;
	private final Boogie2SMT m_Boogie2smt;
	private final Script m_Script;
	
	private final Map<String, TransFormula> m_Proc2OldVarsAssignment;
	private final Map<String, TransFormula> m_Proc2GlobalVarsAssignment;

	public BuchiModGlobalVarManager(BoogieVar unseeded, BoogieVar[] oldRank,
			ModifiableGlobalVariableManager modifiableGlobalVariableManager, 
			Boogie2SMT boogie2Smt) {
		super(modifiableGlobalVariableManager);
		m_Boogie2smt = boogie2Smt;
		m_Unseeded = unseeded;
		m_UnseededOldVar = boogie2Smt.getBoogie2SmtSymbolTable().getOldGlobals().get(unseeded.getIdentifier());
		assert m_UnseededOldVar != null : "oldVar missing";
		m_OldRank = oldRank;
		m_OldRankOldVar = new BoogieVar[oldRank.length];
		for (int i=0; i<oldRank.length; i++) {
			m_OldRankOldVar[i] = boogie2Smt.getBoogie2SmtSymbolTable().getOldGlobals().get(oldRank[i].getIdentifier());
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
		outVars.put(m_UnseededOldVar, m_UnseededOldVar.getTermVariable());
		for (int i=0; i<m_OldRank.length; i++) {
			formula = Util.and(m_Script, formula, oldVarEquality(m_OldRank[i], m_OldRankOldVar[i]));
			inVars.put(m_OldRank[i], m_OldRank[i].getTermVariable());
			outVars.put(m_OldRankOldVar[i], m_OldRankOldVar[i].getTermVariable());
		}
		Term closedFormula = TransFormula.computeClosedFormula(
				formula, inVars, outVars, auxVars, m_Boogie2smt);
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
		outVars.put(m_Unseeded, m_Unseeded.getTermVariable());
		for (int i=0; i<m_OldRank.length; i++) {
			formula = Util.and(m_Script, formula, oldVarEquality(m_OldRank[i], m_OldRankOldVar[i]));
			inVars.put(m_OldRankOldVar[i], m_OldRankOldVar[i].getTermVariable());
			outVars.put(m_OldRank[i], m_OldRank[i].getTermVariable());
		}
		Term closedFormula = TransFormula.computeClosedFormula(
				formula, inVars, outVars, auxVars, m_Boogie2smt);
		TransFormula result = new TransFormula(formula, inVars, outVars, 
				auxVars, branchEncoders, infeasibility, closedFormula);
		return result;
	}


	
	public Term oldVarEquality(BoogieVar var, BoogieVar oldVar) {
		return m_Script.term("=", var.getTermVariable(), oldVar.getTermVariable());
	}


	@Override
	public Map<String, BoogieVar> getGlobals() {
		HashMap<String, BoogieVar> result = 
				new HashMap<String, BoogieVar>(super.getGlobals());
		for (int i=0; i<m_OldRank.length; i++) {
			result.put(m_OldRank[i].getIdentifier(),m_OldRank[i]);
		}
		result.put(m_Unseeded.getIdentifier(),m_Unseeded);
		return result;
	}


	@Override
	public Map<String, BoogieVar> getOldGlobals() {
		HashMap<String, BoogieVar> result = 
				new HashMap<String, BoogieVar>(super.getOldGlobals());
		for (int i=0; i<m_OldRank.length; i++) {
			result.put(m_OldRankOldVar[i].getIdentifier(),m_OldRankOldVar[i]);
		}
		result.put(m_UnseededOldVar.getIdentifier(),m_UnseededOldVar);
		return result;
	}
	
	
	
	
}
