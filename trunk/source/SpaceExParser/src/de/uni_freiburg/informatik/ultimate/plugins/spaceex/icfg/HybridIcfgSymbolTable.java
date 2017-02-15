/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridAutomaton;

/**
 * Class that implements an IIcfgSymbolTable
 * 
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 *
 */
public class HybridIcfgSymbolTable implements IIcfgSymbolTable {
	
	private final Map<String, Set<ILocalProgramVar>> mLocals;
	private final Map<TermVariable, ILocalProgramVar> mTVtoProgVar;
	private final ManagedScript mScript;
	
	/**
	 * Constructor
	 * 
	 * @param script
	 * @param automaton
	 */
	public HybridIcfgSymbolTable(final ManagedScript script, final HybridAutomaton automaton, final String procedure,
			final HybridVariableManager variableManager) {
		mScript = script;
		mLocals = new HashMap<>();
		mTVtoProgVar = new HashMap<>();
		final Set<String> variables = automaton.getGlobalParameters();
		variables.addAll(automaton.getGlobalConstants());
		variables.addAll(automaton.getLocalConstants());
		variables.addAll(automaton.getLocalParameters());
		final Set<ILocalProgramVar> progVars = new HashSet<>();
		for (final String var : variables) {
			// Termvariables for the transformula.
			final TermVariable inVar = script.constructFreshTermVariable(var, script.getScript().sort("Real"));
			final TermVariable outVar = script.constructFreshTermVariable(var, script.getScript().sort("Real"));
			// IProgramVar for the transformula.
			final HybridProgramVar progVar = variableManager.constructProgramVar(var, procedure);
			variableManager.addInVarTermVariable(var, inVar);
			variableManager.addOutVarTermVariable(var, outVar);
			variableManager.addProgramVar(var, progVar);
			mTVtoProgVar.put(inVar, progVar);
			mTVtoProgVar.put(outVar, progVar);
			progVars.add(progVar);
			if (automaton.getLocalConstants().contains(var) || automaton.getGlobalConstants().contains(var)) {
				variableManager.addVarToConstants(var);
			}
		}
		mLocals.put(procedure, progVars);
	}
	
	@Override
	public Set<ILocalProgramVar> getLocals(final String procedurename) {
		return mLocals.get(procedurename);
	}
	
	@Override
	public Set<IProgramNonOldVar> getGlobals() {
		return Collections.emptySet();
	}
	
	@Override
	public Set<IProgramConst> getConstants() {
		return Collections.emptySet();
	}
	
	@Override
	public IProgramVar getProgramVar(final TermVariable tv) {
		return mTVtoProgVar.get(tv);
	}
	
	@Override
	public IProgramConst getProgramConst(final ApplicationTerm at) {
		// TODO Auto-generated method stub
		return null;
	}
	
}
