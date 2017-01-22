/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg;

import java.util.Collections;
import java.util.HashSet;
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
	
	private Set<ILocalProgramVar> mLocals = new HashSet<>();
	private final ManagedScript mScript;
	
	/**
	 * Constructor
	 * 
	 * @param script
	 * @param automaton
	 */
	public HybridIcfgSymbolTable(ManagedScript script, HybridAutomaton automaton, String procedure) {
		mScript = script;
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
	public IProgramVar getProgramVar(TermVariable tv) {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public IProgramConst getProgramConst(ApplicationTerm at) {
		// TODO Auto-generated method stub
		return null;
	}
	
}
