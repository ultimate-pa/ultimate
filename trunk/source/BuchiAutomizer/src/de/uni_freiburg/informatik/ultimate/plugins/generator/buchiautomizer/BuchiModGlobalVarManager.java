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
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula.Infeasibility;

public class BuchiModGlobalVarManager extends ModifiableGlobalVariableManager {
	private final BoogieVar m_Unseeded;
	private final BoogieVar m_OldRank;
	private final BoogieVar m_UnseededOldVar;
	private final BoogieVar m_OldRankOldVar;
	private final Boogie2SMT m_Boogie2smt;
	private final Script m_Script;
	
	private final Map<String, TransFormula> m_Proc2OldVarsAssignment;
	private final Map<String, TransFormula> m_Proc2GlobalVarsAssignment;

	public BuchiModGlobalVarManager(BoogieVar unseeded, BoogieVar oldRank,
			ModifiableGlobalVariableManager modifiableGlobalVariableManager, 
			Boogie2SMT boogie2Smt) {
		super(modifiableGlobalVariableManager);
		m_Boogie2smt = boogie2Smt;
		m_Unseeded = unseeded;
		m_UnseededOldVar = boogie2Smt.getSmt2Boogie().getOldGlobals().get(unseeded.getIdentifier());
		assert m_UnseededOldVar != null : "oldVar missing";
		m_OldRank = oldRank;
		m_OldRankOldVar = boogie2Smt.getSmt2Boogie().getOldGlobals().get(oldRank.getIdentifier());
		assert m_OldRankOldVar != null : "oldVar missing";
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
		formula = Util.and(m_Script, formula, oldVarEquality(m_OldRank, m_OldRankOldVar));
		inVars.put(m_Unseeded, m_Unseeded.getTermVariable());
		inVars.put(m_OldRank, m_OldRank.getTermVariable());
		outVars.put(m_UnseededOldVar, m_UnseededOldVar.getTermVariable());
		outVars.put(m_OldRankOldVar, m_OldRankOldVar.getTermVariable());
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
		formula = Util.and(m_Script, formula, oldVarEquality(m_OldRank, m_OldRankOldVar));
		inVars.put(m_UnseededOldVar, m_UnseededOldVar.getTermVariable());
		inVars.put(m_OldRankOldVar, m_OldRankOldVar.getTermVariable());
		outVars.put(m_Unseeded, m_Unseeded.getTermVariable());
		outVars.put(m_OldRank, m_OldRank.getTermVariable());
		Term closedFormula = TransFormula.computeClosedFormula(
				formula, inVars, outVars, auxVars, m_Boogie2smt);
		TransFormula result = new TransFormula(formula, inVars, outVars, 
				auxVars, branchEncoders, infeasibility, closedFormula);
		return result;
	}


	
	public Term oldVarEquality(BoogieVar var, BoogieVar oldVar) {
		return m_Script.term("=", var.getTermVariable(), oldVar.getTermVariable());
	}
	
	
}
