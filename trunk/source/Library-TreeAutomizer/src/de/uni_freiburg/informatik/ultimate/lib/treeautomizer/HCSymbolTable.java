package de.uni_freiburg.informatik.ultimate.lib.treeautomizer;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashMap;
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
	private final HornClausePredicateSymbol mFalseHornClausePredSym;
	private final HornClausePredicateSymbol mDontCareHornClausePredSym;
	private final HornClausePredicateSymbol mTrueHornClausePredSym;

	private final Map<TermVariable, ApplicationTerm> mTermVarToConst = new HashMap<>();


	public HCSymbolTable(final ManagedScript mgdScript) {
		super();
		mNameToSortsToHornClausePredicateSymbol = new NestedMap2<>();
		mArgPosToSortToHcOutVar = new NestedMap2<>();
		mManagedScript = mgdScript;

		mManagedScript.lock(this);
		mFalseHornClausePredSym = new HornClausePredicateSymbol.HornClauseFalsePredicateSymbol();
		mTrueHornClausePredSym = new HornClausePredicateSymbol.HornClauseTruePredicateSymbol();
		mVersionsMap = new HashMap<>();
		mDontCareHornClausePredSym = new HornClausePredicateSymbol.HornClauseDontCareSymbol();
		mManagedScript.unlock(this);
	}

	final Map<TermVariable, Integer> mVersionsMap;
	
	public TermVariable createFreshVersion(final TermVariable var) {
		int ver = 1;
		if (mVersionsMap.containsKey(var)) {
			ver = mVersionsMap.get(var) + 1;
		}
		return mManagedScript.constructFreshTermVariable(var.getName() + ver, var.getSort());
	}
	
	public HCOutVar getOrConstructHCOutVar(final int argPos, final Sort sort) {
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
	public void add(final IProgramVarOrConst varOrConst) {
		if (mConstructionFinished) {
			throw new IllegalStateException("Construction finished, unable to add new variables or constants.");
		}

		if (varOrConst instanceof IProgramConst) {
			final IProgramConst pc = (IProgramConst) varOrConst;
			mConstants.add(pc);
			mAppTerm2ProgramConst.put(pc.getDefaultConstant(), pc);
		} else if (varOrConst instanceof IProgramVar) {
			final IProgramVar var = (IProgramVar) varOrConst;
			mTermVariable2ProgramVar.put(var.getTermVariable(), var);
			if (var instanceof HCOutVar) {
//				mGlobals.add(nonOldVar);
//				final IProgramOldVar oldVar = nonOldVar.getOldVar();
				mTermVariable2ProgramVar.put(var.getTermVariable(), var);
			} else {
				throw new AssertionError("unknown kind of variable");
			}
		} else {
			throw new AssertionError("unknown kind of variable");
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

			for (int i = 0; i < convertedFunctionParamenterSorts.size(); i++) {
				getOrConstructHCOutVar(i, convertedFunctionParamenterSorts.get(i));
			}
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
	private Sort transferSort(final Sort sort) {
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

	private Sort[] transferSorts(final Sort[] sorts) {
		final Sort[] result = new Sort[sorts.length];
		for (int i = 0; i < sorts.length; i++) {
			result[i] = transferSort(sorts[i]);
		}
		return result;
	}

	/**
	 * We store a constant for each TermVariable (so we can use the constant for HoareTripleChecks later).
	 * Here we update the internal store, and declare the constant.
	 */
	public void registerTermVariable(final TermVariable tv) {
		assert tv == new TermTransferrer(mManagedScript.getScript()).transform(tv);
		if (!mTermVarToConst.containsKey(tv)) {
			mManagedScript.lock(this);
			final ApplicationTerm constant = ProgramVarUtils.constructDefaultConstant(mManagedScript, this, tv.getSort(),
					tv.getName());
			mManagedScript.unlock(this);
			mTermVarToConst.put(tv, constant);
		}
	}

	/**
	 * Every TermVariable that appears in a HornClause has a default constant associated with it, which is declared
	 * up front. (used for hoare triple checks)
	 * @param fv
	 * @return
	 */
	public Term getConstForTermVar(final TermVariable fv) {
		final ApplicationTerm res = mTermVarToConst.get(fv);
		assert res != null;
		return res;
	}

	public boolean hasConstForTermVar(final TermVariable fv) {
		return mTermVarToConst.containsKey(fv);
	}

	public HCOutVar getHCOutVar(final int i, final Sort sort) {
		final HCOutVar result = mArgPosToSortToHcOutVar.get(i, sort);
		if (result == null) {
			throw new AssertionError();
		}
		return result;
	}

}
