package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieOldVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;

/**
 * Contains information about modifiable global variables and provides 
 * auxiliary TransFormulas useful for verification.
 * @author Matthias Heizmann
 */
public class ModifiableGlobalVariableManager {
	
	
	/**
	 * Maps a procedure name to the set of global variables which may be
	 * modified by the procedure. The set of variables is represented as a map
	 * where the identifier of the variable is mapped to the type of the
	 * variable. 
	 */
	private final Map<String,Set<String>> m_ModifiedVars;
	private final Boogie2SMT m_Boogie2smt;
	
	private final Map<String, TransFormula> m_Proc2OldVarsAssignment;
	private final Map<String, TransFormula> m_Proc2GlobalVarsAssignment;
	
	
	
	
	public ModifiableGlobalVariableManager(
			Map<String, Set<String>> modifiedVars,
			Boogie2SMT boogie2smt) {
		m_ModifiedVars = modifiedVars;
		m_Boogie2smt = boogie2smt;
		m_Proc2OldVarsAssignment = new HashMap<String, TransFormula>();
		m_Proc2GlobalVarsAssignment = new HashMap<String, TransFormula>();
	}
	
	protected ModifiableGlobalVariableManager(ModifiableGlobalVariableManager modifiableGlobalVariableManager) {
		m_ModifiedVars = modifiableGlobalVariableManager.m_ModifiedVars;
		m_Boogie2smt = modifiableGlobalVariableManager.m_Boogie2smt;
		m_Proc2OldVarsAssignment = modifiableGlobalVariableManager.m_Proc2OldVarsAssignment;
		m_Proc2GlobalVarsAssignment = modifiableGlobalVariableManager.m_Proc2GlobalVarsAssignment;
	}
	
	/**
	 * Return the set of all global BoogieVars that may be modified by procedure
	 * proc.
	 */
	public Set<BoogieVar> getModifiedBoogieVars(String proc) {
		return getOldVarsAssignment(proc).getInVars().keySet();
	}

	/**
	 * Returns true iff the corresponding non-oldVar of bv is modifiable by
	 * procedure proc.
	 */
	public boolean isModifiable(BoogieOldVar bv, String proc) {
		BoogieNonOldVar bnov = bv.getNonOldVar();
		return getModifiedBoogieVars(proc).contains(bnov);
	}

	/**
	 * Returns true iff the variable bv is modifiable by procedure proc.
	 */
	public boolean isModifiable(BoogieNonOldVar bnov, String proc) {
		return getModifiedBoogieVars(proc).contains(bnov);
	}

	/**
	 * Returns a TransFormula that represents an assignment 
	 * gOld_1,...,gOld_n :=g_1,...,g_n
	 * where g_1,...,g_n are the global variables that can be modified by
	 * procedure proc and gOld_1,...,gOld_n are the corresponding oldvars.
	 */
	public TransFormula getOldVarsAssignment(String proc) {
		TransFormula oldVarsAssignment = m_Proc2OldVarsAssignment.get(proc);
		if (oldVarsAssignment == null) {
			oldVarsAssignment = constructOldVarsAssignment(proc);
			m_Proc2OldVarsAssignment.put(proc, oldVarsAssignment);
		}
		return m_Proc2OldVarsAssignment.get(proc);
	}
	
	
	/**
	 * Returns a TransFormula that represents an assignment 
	 * g_1,...,g_n :=gOld_1,...,gOld_n
	 * where g_1,...,g_n are the global variables that can be modified by
	 * procedure proc and gOld_1,...,gOld_n are the corresponding oldvars.
	 */
	public TransFormula getGlobalVarsAssignment(String proc) {
		TransFormula globalVarsAssignment = m_Proc2GlobalVarsAssignment.get(proc);
		if (globalVarsAssignment == null) {
			globalVarsAssignment = constructGlobalVarsAssignment(proc);
			m_Proc2GlobalVarsAssignment.put(proc, globalVarsAssignment);
		}
		return m_Proc2GlobalVarsAssignment.get(proc);
	}
	
	

	private TransFormula constructOldVarsAssignment(String proc) {
		Set<String> vars = m_ModifiedVars.get(proc);
		if (vars == null) {
			//no global var modified
			vars = new HashSet<String>(0);
		}

		Map<BoogieVar,TermVariable> glob2oldInVars = new HashMap<BoogieVar,TermVariable>();
		Map<BoogieVar,TermVariable> glob2oldOutVars = new HashMap<BoogieVar,TermVariable>();
		Set<TermVariable> glob2oldAllVars = new HashSet<TermVariable>();
		Term glob2oldFormula = m_Boogie2smt.getScript().term("true");
		
		Map<String, BoogieNonOldVar> globals = m_Boogie2smt.getBoogie2SmtSymbolTable().getGlobals();
		for (String modVar : vars) {
			BoogieNonOldVar boogieVar = globals.get(modVar);
			BoogieVar boogieOldVar = boogieVar.getOldVar();
			Sort sort = boogieVar.getDefaultConstant().getSort();
			{
				String nameIn = modVar + "_In";
				TermVariable tvIn = m_Boogie2smt.getScript().variable(nameIn, sort);
				String nameOut = "old(" + modVar + ")" + "_Out";
				TermVariable tvOut = m_Boogie2smt.getScript().variable(nameOut, sort);
				glob2oldInVars.put(boogieVar, tvIn);
				glob2oldOutVars.put(boogieVar, tvIn);
				glob2oldOutVars.put(boogieOldVar, tvOut);
				glob2oldAllVars.add(tvIn);
				glob2oldAllVars.add(tvOut);
				Term assignment = m_Boogie2smt.getScript().term("=", tvOut, tvIn);
				glob2oldFormula = Util.and(m_Boogie2smt.getScript(), glob2oldFormula, assignment);
			}
		}
		HashSet<TermVariable> auxVars = new HashSet<TermVariable>(0);
		HashSet<TermVariable> branchEncoders = new HashSet<TermVariable>(0);
		Term closedFormula = TransFormula.computeClosedFormula(
				glob2oldFormula, glob2oldInVars, glob2oldOutVars, auxVars, false, m_Boogie2smt);
		TransFormula result = new TransFormula(glob2oldFormula, glob2oldInVars,glob2oldOutVars,
				auxVars, branchEncoders,
				TransFormula.Infeasibility.UNPROVEABLE, closedFormula);
		return result;
	}


	
	private TransFormula constructGlobalVarsAssignment(String proc) {
		Set<String> vars = m_ModifiedVars.get(proc);
		if (vars == null) {
			//no global var modified
			vars = new HashSet<String>(0);
		}
	
		Map<BoogieVar,TermVariable> old2globInVars = new HashMap<BoogieVar,TermVariable>();
		Map<BoogieVar,TermVariable> old2globOutVars = new HashMap<BoogieVar,TermVariable>();
		Set<TermVariable> old2globAllVars = new HashSet<TermVariable>();
		Term old2globFormula = m_Boogie2smt.getScript().term("true");
		
		Map<String, BoogieNonOldVar> globals = m_Boogie2smt.getBoogie2SmtSymbolTable().getGlobals();
		for (String modVar : vars) {
			BoogieNonOldVar boogieVar = globals.get(modVar);
			BoogieVar boogieOldVar = boogieVar.getOldVar();
			Sort sort = boogieVar.getDefaultConstant().getSort();
			{
				String nameIn = "old(" + modVar + ")" + "_In";
				TermVariable tvIn = m_Boogie2smt.getScript().variable(nameIn, sort);
				String nameOut = modVar + "_Out";
				TermVariable tvOut = m_Boogie2smt.getScript().variable(nameOut, sort);
				old2globInVars.put(boogieOldVar, tvIn);
				old2globOutVars.put(boogieOldVar, tvIn);
				old2globOutVars.put(boogieVar, tvOut);
				old2globAllVars.add(tvIn);
				old2globAllVars.add(tvOut);
				Term assignment = m_Boogie2smt.getScript().term("=", tvOut, tvIn);
				old2globFormula = Util.and(m_Boogie2smt.getScript(), old2globFormula, assignment);
			}			
		}
		HashSet<TermVariable> auxVars = new HashSet<TermVariable>(0);
		HashSet<TermVariable> branchEncoders = new HashSet<TermVariable>(0);
		Term closedFormula = TransFormula.computeClosedFormula(
				old2globFormula, old2globInVars, old2globOutVars, auxVars, false, m_Boogie2smt);
		TransFormula result = new TransFormula(old2globFormula, old2globInVars, old2globOutVars,
				auxVars, branchEncoders, TransFormula.Infeasibility.UNPROVEABLE,closedFormula);
		return result;
	}
	
	/**
	 * Return global variables;
	 */
	public Map<String, BoogieNonOldVar> getGlobals() {
		return m_Boogie2smt.getBoogie2SmtSymbolTable().getGlobals();
	}

}
