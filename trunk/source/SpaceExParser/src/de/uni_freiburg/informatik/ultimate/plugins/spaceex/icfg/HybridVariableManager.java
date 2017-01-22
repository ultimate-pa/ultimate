package de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class HybridVariableManager {
	
	private ManagedScript mScript;
	private Map<String, HybridProgramVar> mVar2ProgramVar;
	private Map<HybridProgramVar, String> mProgramVar2Var;
	private Map<String, TermVariable> mVar2InVarTermVariable;
	private Map<String, TermVariable> mVar2OutVarTermVariable;
	private Map<TermVariable, String> mTermVariable2Var;
	private Map<TermVariable, String> mTermVariable2InVar;
	private Map<TermVariable, String> mTermVariable2OutVar;
	
	public HybridVariableManager(ManagedScript script) {
		mScript = script;
		mVar2ProgramVar = new HashMap<>();
		mProgramVar2Var = new HashMap<>();
		mVar2InVarTermVariable = new HashMap<>();
		mVar2OutVarTermVariable = new HashMap<>();
		mTermVariable2InVar = new HashMap<>();
		mTermVariable2OutVar = new HashMap<>();
	}
	
	public HybridProgramVar constructProgramVar(final String identifier, final String procedure) {
		final Sort sort = mScript.getScript().sort("Real");
		final String id = identifier;
		final TermVariable termVariable = mScript.variable(id, sort);
		final ApplicationTerm defaultConstant = ProgramVarUtils.constructDefaultConstant(mScript, this, sort, id);
		final ApplicationTerm primedConstant = ProgramVarUtils.constructPrimedConstant(mScript, this, sort, id);
		HybridProgramVar progVar = new HybridProgramVar(termVariable, defaultConstant, primedConstant, id, procedure);
		mVar2ProgramVar.put(identifier, progVar);
		mProgramVar2Var.put(progVar, identifier);
		return progVar;
	}
	
	public Map<String, HybridProgramVar> getVar2ProgramVar() {
		return mVar2ProgramVar;
	}
	
	public Map<HybridProgramVar, String> getProgramVar2Var() {
		return mProgramVar2Var;
	}
	
	public Map<String, TermVariable> getVar2InVarTermVariable() {
		return mVar2InVarTermVariable;
	}
	
	public Map<String, TermVariable> getVar2OutVarTermVariable() {
		return mVar2OutVarTermVariable;
	}
	
	public Map<TermVariable, String> getTermVariable2InVar() {
		return mTermVariable2InVar;
	}
	
	public Map<TermVariable, String> getTermVariable2OutVar() {
		return mTermVariable2OutVar;
	}
	
	public void addProgramVar(String varName, HybridProgramVar programvar) {
		mVar2ProgramVar.put(varName, programvar);
		mProgramVar2Var.put(programvar, varName);
	}
	
	public void addInVarTermVariable(String varName, TermVariable termVariable) {
		mVar2InVarTermVariable.put(varName, termVariable);
		mTermVariable2InVar.put(termVariable, varName);
	}
	
	public void addOutVarTermVariable(String varName, TermVariable termVariable) {
		mVar2OutVarTermVariable.put(varName, termVariable);
		mTermVariable2OutVar.put(termVariable, varName);
	}
	
}
