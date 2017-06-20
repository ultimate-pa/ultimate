package de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class HCPredicateSymbolTable {
	
	private final Map<Set<HornClausePredicateSymbol>, Set<HornClausePredicateSymbol>> originalVersion = new HashMap<>();
	private final Map<Set<HornClausePredicateSymbol>, ArrayList<Set<HornClausePredicateSymbol>>> versions = new HashMap<>();
	
	public HCPredicateSymbolTable(ManagedScript mBackendSmtSolver) {
		// TODO Auto-generated constructor stub
	}

	public Set<HornClausePredicateSymbol> getOrCreateOriginalVersion(final Set<HornClausePredicateSymbol> p) {
		if (!originalVersion.containsKey(p)) {
			versions.put(p, new ArrayList<>());
			originalVersion.put(p, p);
		}
		return originalVersion.get(p);
	}
	public void finishConstruction() {}
	
	public Set<HornClausePredicateSymbol> createVersion(final Set<HornClausePredicateSymbol> p) {
		// TODO:
		final Set<HornClausePredicateSymbol> t = getOrCreateOriginalVersion(p);
		//final HornClause res = t.versionHornClause(versions.get(t).size());
		//versions.HornClausePredicateSymbol(t).add(res);
		//originalVersion.put(res, t);
		//return res;
		return t;
	}
	
}
