package de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
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
//	final Map<FunctionSymbol, HornClausePredicateSymbol> mNameToHornClausePredicateSymbol;
	final NestedMap2<String, List<Sort>, HornClausePredicateSymbol> mNameToSortsToHornClausePredicateSymbol;
	final NestedMap2<HornClausePredicateSymbol, Integer, HCVar> mHCPredSymbolToPositionToHCVar;
	private HornClausePredicateSymbol mFalseHornClausePredSym;
	private HornClausePredicateSymbol mDontCareHornClausePredSym;
	private HornClausePredicateSymbol mTrueHornClausePredSym;

	public HCSymbolTable(ManagedScript mgdScript) {
		super();
		mNameToSortsToHornClausePredicateSymbol = new NestedMap2<>();
		mHCPredSymbolToPositionToHCVar = new NestedMap2<>();
		mManagedScript = mgdScript;
		
		mManagedScript.lock(this);
//		FunctionSymbol falseFunctionSymbol = ((ApplicationTerm) mManagedScript.term(this, "false")).getFunction();
		mFalseHornClausePredSym = new HornClausePredicateSymbol.HornClauseFalsePredicateSymbol();
//		FunctionSymbol trueFunctionSymbol = ((ApplicationTerm) mManagedScript.term(this, "true")).getFunction();
		mTrueHornClausePredSym = new HornClausePredicateSymbol.HornClauseTruePredicateSymbol();
		
		// TODO a bit hacky.. --> is there a more elegant solution?
		//String dontCare = HornUtilConstants.DONTCARE;
		//mManagedScript.declareFun(this, dontCare, new Sort[0], trueFunctionSymbol.getReturnSort());
		//FunctionSymbol dontCareFunctionSymbol = ((ApplicationTerm) mManagedScript.term(this, dontCare)).getFunction();
		mDontCareHornClausePredSym = new HornClausePredicateSymbol.HornClauseDontCareSymbol();//dontCareFunctionSymbol);
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
	
	public HornClausePredicateSymbol getOrConstructHornClausePredicateSymbol(
			final String functionName, final Sort[] functionParamenterSorts) {
		final List<Sort> convertedFunctionParamenterSorts = Arrays.asList(transferSorts(functionParamenterSorts));
		
		HornClausePredicateSymbol result = mNameToSortsToHornClausePredicateSymbol.get(
				functionName, 
				convertedFunctionParamenterSorts);
		if (result == null) {
			result = new HornClausePredicateSymbol(this, functionName, convertedFunctionParamenterSorts);
			mNameToSortsToHornClausePredicateSymbol.put(functionName, convertedFunctionParamenterSorts, result);
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
	
	
	/*
	 * TODO: copied from TermTransferrer --> do something nicer..
	 */
	private Sort transferSort(Sort sort) {
		final Sort[] arguments = transferSorts(sort.getArguments());
		final BigInteger[] indices = sort.getIndices();
		Sort result;
		try {
			result = mManagedScript.getScript().sort(sort.getName(), indices, arguments);
		} catch (final SMTLIBException e) {
			if (e.getMessage().equals("Sort " + sort.getName() + " not declared")) {
				mManagedScript.getScript().declareSort(sort.getName(), sort.getArguments().length);
				result = mManagedScript.getScript().sort(sort.getName(), arguments);
			} else {
				throw e;
			}
		}
		return result;
	}
	
	private Sort[] transferSorts(Sort[] sorts) {
		final Sort[] result = new Sort[sorts.length];
		for (int i=0; i<sorts.length; i++) {
			result[i] = transferSort(sorts[i]);
		}
		return result;
	}

}
