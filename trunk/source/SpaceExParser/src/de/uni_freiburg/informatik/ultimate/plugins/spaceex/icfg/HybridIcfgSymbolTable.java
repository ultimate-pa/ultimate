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
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridAutomaton;

/**
 * Class that implements an IIcfgSymbolTable
 * 
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 *
 */
public class HybridIcfgSymbolTable implements IIcfgSymbolTable {
	
	private Set<ILocalProgramVar> mLocals = new HashSet<>();
	private Map<TermVariable, IProgramVar> mVars = new HashMap<>();
	private final ManagedScript mScript;
	private final HybridAutomaton mAutomaton;
	
	/**
	 * Constructor
	 * 
	 * @param script
	 * @param automaton
	 */
	public HybridIcfgSymbolTable(ManagedScript script, HybridAutomaton automaton, String procedure) {
		mScript = script;
		mAutomaton = automaton;
		// we can merge all variables into one set.
		final Set<String> variables = automaton.getGlobalParameters();
		variables.addAll(automaton.getGlobalConstants());
		variables.addAll(automaton.getLocalConstants());
		variables.addAll(automaton.getLocalParameters());
		variables.forEach(var -> {
			mVars.put(script.constructFreshTermVariable(var, script.getScript().sort("Real")),
					constructProgramVar(var, procedure));
			// mLocals.add(constructLocalProgramVar(var, procedure));
		});
	}
	
	private HybridLocalProgramVar constructLocalProgramVar(String identifier, String procedure) {
		final Sort sort = mScript.getScript().sort("Real");
		final String id = identifier;
		final TermVariable termVariable = mScript.variable(id, sort);
		final ApplicationTerm defaultConstant = ProgramVarUtils.constructDefaultConstant(mScript, this, sort, id);
		final ApplicationTerm primedConstant = ProgramVarUtils.constructPrimedConstant(mScript, this, sort, id);
		return new HybridLocalProgramVar(termVariable, defaultConstant, primedConstant, id, procedure);
	}
	
	public HybridProgramVar constructProgramVar(final String identifier, final String procedure) {
		final Sort sort = mScript.getScript().sort("Real");
		final String id = identifier;
		final TermVariable termVariable = mScript.variable(id, sort);
		final ApplicationTerm defaultConstant = ProgramVarUtils.constructDefaultConstant(mScript, this, sort, id);
		final ApplicationTerm primedConstant = ProgramVarUtils.constructPrimedConstant(mScript, this, sort, id);
		return new HybridProgramVar(termVariable, defaultConstant, primedConstant, id, procedure);
	}
	
	/*
	 * Function to construct a ProgramNonOldVar
	 */
	public HybridProgramNonOldVar constructProgramNonOldVar(final String identifier, final String procedure) {
		final Sort sort = mScript.getScript().sort("Real");
		final String id = identifier;
		final TermVariable termVariable = mScript.variable(id, sort);
		final ApplicationTerm defaultConstant = ProgramVarUtils.constructDefaultConstant(mScript, this, sort, id);
		final ApplicationTerm primedConstant = ProgramVarUtils.constructPrimedConstant(mScript, this, sort, id);
		return new HybridProgramNonOldVar(termVariable, defaultConstant, primedConstant, id);
	}
	
	@Override
	public Set<ILocalProgramVar> getLocals(final String procedurename) {
		return mLocals;
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
		return mVars.get(tv);
	}
	
	@Override
	public IProgramConst getProgramConst(final ApplicationTerm at) {
		return new IProgramConst() {
			
			@Override
			public String getGloballyUniqueId() {
				return "asd";
			}
			
			@Override
			public boolean isGlobal() {
				return false;
			}
			
			@Override
			public Term getTerm() {
				return mScript.getScript().term("false");
			}
			
			@Override
			public String getIdentifier() {
				// TODO Auto-generated method stub
				return null;
			}
			
			@Override
			public ApplicationTerm getDefaultConstant() {
				// TODO Auto-generated method stub
				return null;
			}
		};
	}
	
}
