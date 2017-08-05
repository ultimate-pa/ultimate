package de.uni_freiburg.informatik.ultimate.lib.treeautomizer;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

public class HCSymbolTable extends DefaultIcfgSymbolTable {
	
	private final ManagedScript mManagedScript;

	private final NestedMap2<String, List<Sort>, HornClausePredicateSymbol> mNameToSortsToHornClausePredicateSymbol;
//	private final NestedMap3<Integer, Integer, Sort, HCInVar> mInPredPosToArgPosToSortToHcInVar;
	private final NestedMap2<Integer, Sort, HCOutVar> mArgPosToSortToHcOutVar;
	
//	final NestedMap2<HornClausePredicateSymbol, Integer, HCVar> mHCPredSymbolToPositionToHCVar;
	private HornClausePredicateSymbol mFalseHornClausePredSym;
	private HornClausePredicateSymbol mDontCareHornClausePredSym;
	private HornClausePredicateSymbol mTrueHornClausePredSym;

	private Map<TermVariable, ApplicationTerm> mTermVarToConst;


	public HCSymbolTable(ManagedScript mgdScript) {
		super();
		mNameToSortsToHornClausePredicateSymbol = new NestedMap2<>();
//		mInPredPosToArgPosToSortToHcInVar = new NestedMap3<>();
		mArgPosToSortToHcOutVar = new NestedMap2<>();
//		mHCPredSymbolToPositionToHCVar = new NestedMap2<>();
		mManagedScript = mgdScript;
		
		mManagedScript.lock(this);
		mFalseHornClausePredSym = new HornClausePredicateSymbol.HornClauseFalsePredicateSymbol();
		mTrueHornClausePredSym = new HornClausePredicateSymbol.HornClauseTruePredicateSymbol();
		
		mDontCareHornClausePredSym = new HornClausePredicateSymbol.HornClauseDontCareSymbol();
		mManagedScript.unlock(this);
	}

//	public HCInVar getOrConstructHCInVar(int predPos, int argPos, Sort sort) {
//		HCInVar result = mInPredPosToArgPosToSortToHcInVar.get(predPos, argPos, sort);
//
//		if (result == null) {
//			final String varName = String.format("HcInVar_%d_%d_%s", predPos, argPos, sort);
//
//			mManagedScript.lock(this);
//			final TermVariable variable = mManagedScript.variable(varName, sort);
//			final ApplicationTerm defaultConstant = ProgramVarUtils.constructDefaultConstant(mManagedScript, this, sort,
//					varName);
//			final ApplicationTerm primedConstant = ProgramVarUtils.constructPrimedConstant(mManagedScript, this, sort, 
//					varName);
//			mManagedScript.unlock(this);
//			
//			result = new HCInVar(
//					predPos,
//					argPos, 
//					sort,
//					variable,
//					defaultConstant,
//					primedConstant);
//			mInPredPosToArgPosToSortToHcInVar.put(predPos, argPos, sort, result);
//			add(result);
//		}
//		assert result.getTermVariable().getSort() == sort;
//
//		return result;
//	}
	public HCOutVar getOrConstructHCOutVar(int argPos, Sort sort) {
		HCOutVar result = mArgPosToSortToHcOutVar.get(argPos, sort);

		if (result == null) {
			final String varName = String.format("HcOutVar_%d_%s", argPos, sort);

			mManagedScript.lock(this);
			final TermVariable variable = mManagedScript.variable(varName, sort);
			final ApplicationTerm defaultConstant = ProgramVarUtils.constructDefaultConstant(mManagedScript, this, sort,
					varName);
			final ApplicationTerm primedConstant = ProgramVarUtils.constructPrimedConstant(mManagedScript, this, sort, 
					varName);
			mManagedScript.unlock(this);
			
			result = new HCOutVar(
					argPos, 
					sort,
					variable,
					defaultConstant,
					primedConstant);
			mArgPosToSortToHcOutVar.put(argPos, sort, result);
			add(result);
		}
		assert result.getTermVariable().getSort() == sort;

		return result;
	}
	
	
	
	@Override
	public void add(IProgramVarOrConst varOrConst) {
		if (varOrConst instanceof IProgramConst) {
			assert false : "TODO: support constants";
			super.add(varOrConst); 
		} else if (varOrConst instanceof IProgramVar) {
			IProgramVar var = (IProgramVar) varOrConst;
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
	
	/**
	 * We store a constant for each TermVariable (so we can use the constant for HoareTripleChecks later).
	 * Here we update the internal store, and declare the constant.
	 */
	public void registerTermVariable(TermVariable tv) {
		assert tv == new TermTransferrer(mManagedScript.getScript()).transform(tv);
		mManagedScript.lock(this);
		final ApplicationTerm constant = ProgramVarUtils.constructDefaultConstant(mManagedScript, this, tv.getSort(), 
				tv.getName());
		mManagedScript.unlock(this);
		mTermVarToConst.put(tv, constant);
	}

	public Term getConstForTermVar(TermVariable fv) {
		final ApplicationTerm res = mTermVarToConst.get(fv);
		assert res != null;
		return res;
	}

}
