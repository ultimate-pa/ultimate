package de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

public class HCSymbolTable extends DefaultIcfgSymbolTable {
	
	final ManagedScript mManagedScript;
	final Map<FunctionSymbol, HornClausePredicateSymbol> mNameToHornClausePredicateSymbol;
	final NestedMap2<HornClausePredicateSymbol, Integer, HCVar> mHCPredSymbolToPositionToHCVar;

	public HCSymbolTable(ManagedScript mgdScript) {
		super();
		mNameToHornClausePredicateSymbol = new HashMap<>();
		mHCPredSymbolToPositionToHCVar = new NestedMap2<>();
		mManagedScript = mgdScript;
	}

	public HCVar getOrConstructHCVar(final HornClausePredicateSymbol predSymbol, final int pos, final Sort sort) {
		HCVar result = mHCPredSymbolToPositionToHCVar.get(predSymbol, pos);

		if (result == null) {
			final String varName = predSymbol.getName() + "_" + pos;
			final String varNamePrimed = varName + "'";
			result = new HCVar(
					predSymbol, 
					pos, 
					mManagedScript.constructFreshTermVariable(varName, sort), 
					(ApplicationTerm) mManagedScript.term(this, varName), 
					(ApplicationTerm) mManagedScript.term(this, varNamePrimed));
			mHCPredSymbolToPositionToHCVar.put(predSymbol, pos, result);
			add(result);
		}
		assert result.getTermVariable().getSort() == sort;

		return result;
	}
	
	public HornClausePredicateSymbol getOrConstructHornClausePredicateSymbol(final FunctionSymbol function) {
		HornClausePredicateSymbol result = mNameToHornClausePredicateSymbol.get(function);
		if (result == null) {
			result = new HornClausePredicateSymbol(this, function);
			mNameToHornClausePredicateSymbol.put(function, result);
		}
		return result;
	}
	
	
	public HornClausePredicateSymbol getFalseHornClausePredicateSymbol() {
		// TODO: implement;
		return null;
	}

	public HornClausePredicateSymbol getTrueHornClausePredicateSymbol() {
		// TODO: implement;
		return null;
	}

	public HornClausePredicateSymbol getDontCareHornClausePredicateSymbol() {
		// TODO: implement;
		return null;
	}

}
