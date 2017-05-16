package de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridAutomaton;

public class HybridVariableManager {

	private ManagedScript mScript;
	private final Map<String, HybridProgramVar> mVarToProgramVar;
	private final Map<HybridProgramVar, String> mProgramVarToVar;
	private final Map<String, TermVariable> mVarToInVarTermVariable;
	private final Map<String, TermVariable> mVarToOutVarTermVariable;
	private final Set<String> mConstants;
	private Map<TermVariable, String> mTermVariableToVar;
	private final Map<TermVariable, String> mTermVariableToInVar;
	private final Map<TermVariable, String> mTermVariableToOutVar;
	// Map that holds the parallel composition of each preference group.
	private Map<Integer, HybridAutomaton> mGroupIdToParallelComposition;

	public HybridVariableManager() {
		mScript = null;
		mVarToProgramVar = new HashMap<>();
		mProgramVarToVar = new HashMap<>();
		mVarToInVarTermVariable = new HashMap<>();
		mVarToOutVarTermVariable = new HashMap<>();
		mTermVariableToInVar = new HashMap<>();
		mTermVariableToOutVar = new HashMap<>();
		mConstants = new HashSet<>();
		mGroupIdToParallelComposition = new HashMap<>();
	}

	public HybridProgramVar constructProgramVar(final String identifier, final String procedure) {
		final Sort sort = SmtSortUtils.getRealSort(mScript);
		mScript.lock(this);
		final String id = identifier;
		final TermVariable termVariable = mScript.variable(id, sort);
		final ApplicationTerm defaultConstant = ProgramVarUtils.constructDefaultConstant(mScript, this, sort, id);
		final ApplicationTerm primedConstant = ProgramVarUtils.constructPrimedConstant(mScript, this, sort, id);
		final HybridProgramVar progVar =
				new HybridProgramVar(termVariable, defaultConstant, primedConstant, id, procedure);
		mVarToProgramVar.put(identifier, progVar);
		mProgramVarToVar.put(progVar, identifier);
		mScript.unlock(this);
		return progVar;
	}

	public Map<String, HybridProgramVar> getVarToProgramVar() {
		return mVarToProgramVar;
	}

	public Map<HybridProgramVar, String> getProgramVarToVar() {
		return mProgramVarToVar;
	}

	public Map<String, TermVariable> getVarToInVarTermVariable() {
		return mVarToInVarTermVariable;
	}

	public Map<String, TermVariable> getVarToOutVarTermVariable() {
		return mVarToOutVarTermVariable;
	}

	public Map<TermVariable, String> getTermVariableToInVar() {
		return mTermVariableToInVar;
	}

	public Map<TermVariable, String> getTermVariableToOutVar() {
		return mTermVariableToOutVar;
	}

	public void addProgramVar(final String varName, final HybridProgramVar programvar) {
		mVarToProgramVar.put(varName, programvar);
		mProgramVarToVar.put(programvar, varName);
	}

	public void addInVarTermVariable(final String varName, final TermVariable termVariable) {
		mVarToInVarTermVariable.put(varName, termVariable);
		mTermVariableToInVar.put(termVariable, varName);
	}

	public void addOutVarTermVariable(final String varName, final TermVariable termVariable) {
		mVarToOutVarTermVariable.put(varName, termVariable);
		mTermVariableToOutVar.put(termVariable, varName);
	}

	public Set<String> getConstants() {
		return mConstants;
	}

	public void addVarToConstants(final String var) {
		mConstants.add(var);
	}

	public void addVarsToConstants(final Set<String> constants) {
		mConstants.addAll(constants);
	}

	public Map<Integer, HybridAutomaton> getGroupIdToParallelComposition() {
		return mGroupIdToParallelComposition;
	}

	public void setGroupIdToParallelComposition(final Map<Integer, HybridAutomaton> groupIdToParallelComposition) {
		mGroupIdToParallelComposition = groupIdToParallelComposition;
	}

	public void setScript(final ManagedScript script) {
		mScript = script;
	}

}
