package de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

public class HCSymbolTable extends DefaultIcfgSymbolTable {
	
	final ManagedScript mManagedScript;
	final Map<FunctionSymbol, HornClausePredicateSymbol> mNameToHornClausePredicateSymbol;
	final NestedMap2<HornClausePredicateSymbol, Integer, HCVar> mHCPredSymbolToPositionToHCVar;
	private HornClausePredicateSymbol mFalseHornClausePredSym;
	private HornClausePredicateSymbol mDontCareHornClausePredSym;
	private HornClausePredicateSymbol mTrueHornClausePredSym;

	public HCSymbolTable(ManagedScript mgdScript) {
		super();
		mNameToHornClausePredicateSymbol = new HashMap<>();
		mHCPredSymbolToPositionToHCVar = new NestedMap2<>();
		mManagedScript = mgdScript;
		
		mManagedScript.lock(this);
		FunctionSymbol falseFunctionSymbol = ((ApplicationTerm) mManagedScript.term(this, "false")).getFunction();
		mFalseHornClausePredSym = new HornClausePredicateSymbol.HornClauseFalsePredicateSymbol(falseFunctionSymbol);
		FunctionSymbol trueFunctionSymbol = ((ApplicationTerm) mManagedScript.term(this, "true")).getFunction();
		mTrueHornClausePredSym = new HornClausePredicateSymbol.HornClauseTruePredicateSymbol(trueFunctionSymbol);
		
		// TODO a bit hacky.. --> is there a more elegant solution?
		//String dontCare = HornUtilConstants.DONTCARE;
		//mManagedScript.declareFun(this, dontCare, new Sort[0], trueFunctionSymbol.getReturnSort());
		//FunctionSymbol dontCareFunctionSymbol = ((ApplicationTerm) mManagedScript.term(this, dontCare)).getFunction();
		mDontCareHornClausePredSym = new HornClausePredicateSymbol.HornClauseDontCareSymbol(trueFunctionSymbol);//dontCareFunctionSymbol);
		mManagedScript.unlock(this);
	}

	public HCVar getOrConstructHCVar(final HornClausePredicateSymbol predSymbol, final int pos, final Sort sort) {
		HCVar result = mHCPredSymbolToPositionToHCVar.get(predSymbol, pos);

		if (result == null) {
			final String varName = predSymbol.getName() + "_" + pos;
			mManagedScript.lock(this);
			
			TermVariable variable = mManagedScript.variable(varName, sort);
			ApplicationTerm defaultConstant = ProgramVarUtils.constructDefaultConstant(mManagedScript, this, sort, varName);
			ApplicationTerm primedConstant = ProgramVarUtils.constructPrimedConstant(mManagedScript, this, sort, varName);
			
			result = new HCVar(
					predSymbol, 
					pos, 
//					mManagedScript.constructFreshTermVariable(varName, sort), 
					variable,
					defaultConstant,
					primedConstant);
//					(ApplicationTerm) mManagedScript.term(this, varName), 
//					(ApplicationTerm) mManagedScript.term(this, varNamePrimed));
			mHCPredSymbolToPositionToHCVar.put(predSymbol, pos, result);
			mManagedScript.unlock(this);
			add(result);
		}
		assert result.getTermVariable().getSort() == sort;

		return result;
	}
	
	
	@Override
	public void add(IProgramVarOrConst varOrConst) {
		if (varOrConst instanceof IProgramConst) {
			assert false : "TODO: support constants";
			super.add(varOrConst); //maybe like this??. TODO
		} else if (varOrConst instanceof HCVar) {
			HCVar var = (HCVar) varOrConst;
			mTermVariable2ProgramVar.put(var.getTermVariable(), var);
		}
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
		return mFalseHornClausePredSym;
	}

	public HornClausePredicateSymbol getTrueHornClausePredicateSymbol() {
		return mTrueHornClausePredSym;
	}

	public HornClausePredicateSymbol getDontCareHornClausePredicateSymbol() {
		return mDontCareHornClausePredSym;
	}

}
