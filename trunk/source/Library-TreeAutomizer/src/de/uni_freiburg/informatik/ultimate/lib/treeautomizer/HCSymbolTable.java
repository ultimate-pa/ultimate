package de.uni_freiburg.informatik.ultimate.lib.treeautomizer;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ITerm2ExpressionSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;

/**
 * Stores runtime information concerning a set of constrained HornClauses centrally.
 * Eg. to pass information from a parser of a Horn clause format to a plugin like {@link TreeAutomizer} or
 * {@link ChcToBooge} this could be used.
 *
 * FIXME: it is rather dubitable if this should be called a symbol table, and should not extend one either..
 *
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
//public class HCSymbolTable implements ITerm2ExpressionSymbolTable {
public class HCSymbolTable extends DefaultIcfgSymbolTable implements ITerm2ExpressionSymbolTable {

	private final ManagedScript mManagedScript;

	private final NestedMap2<String, List<Sort>, HornClausePredicateSymbol> mNameToSortsToHornClausePredicateSymbol;
//	private final NestedMap3<Integer, Integer, Sort, HCInVar> mInPredPosToArgPosToSortToHcInVar;
	private final NestedMap2<Integer, Sort, HcBodyVar> mArgPosToSortToHcOutVar;

//	final NestedMap2<HornClausePredicateSymbol, Integer, HCVar> mHCPredSymbolToPositionToHCVar;
	private final HornClausePredicateSymbol mFalseHornClausePredSym;
	private final HornClausePredicateSymbol mDontCareHornClausePredSym;
	private final HornClausePredicateSymbol mTrueHornClausePredSym;

	private final Map<TermVariable, ApplicationTerm> mTermVarToConst = new HashMap<>();

	final Map<TermVariable, Integer> mVersionsMap;

	private final NestedMap3<String, Integer, Sort, HcHeadVar> mPredSymNameToIndexToSortToHcHeadVar;
	private final NestedMap3<String, Integer, Sort, HcBodyVar> mPredSymNameToIndexToSortToHcBodyVar;

	private final Map<TermVariable, IProgramVar> mTermVarToProgramVar;


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
		mPredSymNameToIndexToSortToHcHeadVar = new NestedMap3<>();
		mPredSymNameToIndexToSortToHcBodyVar = new NestedMap3<>();
		mTermVarToProgramVar = new HashMap<>();
	}

	public TermVariable createFreshVersion(final TermVariable var) {
		int ver = 1;
		if (mVersionsMap.containsKey(var)) {
			ver = mVersionsMap.get(var) + 1;
		}
		return mManagedScript.constructFreshTermVariable(var.getName() + ver, var.getSort());
	}

//	public HcBodyVar getOrConstructHCOutVar(final int argPos, final Sort sort) {
//		HcBodyVar result = mArgPosToSortToHcOutVar.get(argPos, sort);
//
//		if (result == null) {
//			final String varName = String.format("HcOutVar_%d_%s", argPos, sort);
//
//			mManagedScript.lock(this);
//			final TermVariable variable = mManagedScript.variable(varName, sort);
//			final ApplicationTerm defaultConstant = ProgramVarUtils.constructDefaultConstant(mManagedScript, this, sort,
//					varName);
//			final ApplicationTerm primedConstant = ProgramVarUtils.constructPrimedConstant(mManagedScript, this, sort,
//					varName);
//			mManagedScript.unlock(this);
//
//			result = new HcBodyVar(
//					argPos,
//					sort,
//					variable,
//					defaultConstant,
//					primedConstant);
//			mArgPosToSortToHcOutVar.put(argPos, sort, result);
//			add(result);
//		}
//		assert result.getTermVariable().getSort() == sort;
//
//		return result;
//	}

//	@Override
//	public void add(final IProgramVarOrConst varOrConst) {
//		if (mConstructionFinished) {
//			throw new IllegalStateException("Construction finished, unable to add new variables or constants.");
//		}
//
//		if (varOrConst instanceof IProgramConst) {
//			final IProgramConst pc = (IProgramConst) varOrConst;
//			mConstants.add(pc);
//			mAppTerm2ProgramConst.put(pc.getDefaultConstant(), pc);
//		} else if (varOrConst instanceof IProgramVar) {
//			final IProgramVar var = (IProgramVar) varOrConst;
//			mTermVariable2ProgramVar.put(var.getTermVariable(), var);
//			if (var instanceof HcBodyVar) {
////				mGlobals.add(nonOldVar);
////				final IProgramOldVar oldVar = nonOldVar.getOldVar();
//				mTermVariable2ProgramVar.put(var.getTermVariable(), var);
//			} else {
//				throw new AssertionError("unknown kind of variable");
//			}
//		} else {
//			throw new AssertionError("unknown kind of variable");
//		}
//	}



	public HornClausePredicateSymbol getOrConstructHornClausePredicateSymbol(
			final String functionName, final Sort[] functionParamenterSorts) {
		final List<Sort> convertedFunctionParamenterSorts = Arrays.asList(transferSorts(functionParamenterSorts));

		HornClausePredicateSymbol result = mNameToSortsToHornClausePredicateSymbol.get(
				functionName,
				convertedFunctionParamenterSorts);
		if (result == null) {
			result = new HornClausePredicateSymbol(this, functionName, convertedFunctionParamenterSorts);
			mNameToSortsToHornClausePredicateSymbol.put(functionName, convertedFunctionParamenterSorts, result);

			mManagedScript.lock(this);
			mManagedScript.declareFun(this, result.getName(),
					convertedFunctionParamenterSorts.toArray(new Sort[convertedFunctionParamenterSorts.size()]),
					mManagedScript.getScript().sort("Bool"));
			mManagedScript.unlock(this);
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

//	/**
//	 * We store a constant for each TermVariable (so we can use the constant for HoareTripleChecks later).
//	 * Here we update the internal store, and declare the constant.
//	 */
//	public void registerTermVariable(final TermVariable tv) {
//		assert tv == new TermTransferrer(mManagedScript.getScript()).transform(tv);
//		if (!mTermVarToConst.containsKey(tv)) {
//			mManagedScript.lock(this);
//			final ApplicationTerm constant = ProgramVarUtils.constructDefaultConstant(mManagedScript, this, tv.getSort(),
//					tv.getName());
//			mManagedScript.unlock(this);
//			mTermVarToConst.put(tv, constant);
//		}
//	}
	public HcHeadVar getHeadVar(final String predSymName, final int index, final Sort sort) {
		final Sort transferredSort = transferSort(sort);
		final HcHeadVar result = mPredSymNameToIndexToSortToHcHeadVar.get(predSymName, index, transferredSort);//mIndexToSortToHcHeadVar.get(index, transferredSort);
		assert result != null;
		return result;
	}

	public HcHeadVar getOrConstructHeadVar(final String predSymName, final int index, final Sort sort) {
		final Sort transferredSort = transferSort(sort);
		HcHeadVar result = mPredSymNameToIndexToSortToHcHeadVar.get(predSymName, index, transferredSort);
		if (result == null) {
			mManagedScript.lock(this);
			result = new HcHeadVar(predSymName, index, transferredSort, mManagedScript, this);
			mManagedScript.unlock(this);
			mPredSymNameToIndexToSortToHcHeadVar.put(predSymName, index, transferredSort, result);
			mTermVarToProgramVar.put(result.getTermVariable(), result);
		}
		return result;
	}

	public HcBodyVar getOrConstructBodyVar(final String predSymName, final int index, final Sort sort) {
		final Sort transferredSort = transferSort(sort);
		HcBodyVar result = mPredSymNameToIndexToSortToHcBodyVar.get(predSymName, index, transferredSort);
		if (result == null) {
			mManagedScript.lock(this);
			result = new HcBodyVar(predSymName, index, transferredSort, mManagedScript, this);
			mManagedScript.unlock(this);
			mPredSymNameToIndexToSortToHcBodyVar.put(predSymName, index, transferredSort, result);
			mTermVarToProgramVar.put(result.getTermVariable(), result);
		}
		return result;
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

	public HcBodyVar getHCOutVar(final int i, final Sort sort) {
		final HcBodyVar result = mArgPosToSortToHcOutVar.get(i, sort);
		if (result == null) {
			throw new AssertionError();
		}
		return result;
	}

	public String getHeadVarName(final int i, final Sort sort) {
		return "headvar_" + i + "_" + sort.getName();
	}

	@Override
	public BoogieConst getProgramConst(final ApplicationTerm term) {
		throw new AssertionError();
	}

	@Override
	public Map<String, String> getSmtFunction2BoogieFunction() {
		throw new UnsupportedOperationException();
	}


	@Override
	public IProgramVar getProgramVar(final TermVariable tv) {
		final IProgramVar result = mTermVarToProgramVar.get(tv);
		assert result != null;
		return result;
	}

	@Override
	public ILocation getLocation(final IProgramVar pv) {
		return new BoogieLocation(pv.getGloballyUniqueId(), 0, 0, 0, 0);
	}

	@Override
	public de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation
			getDeclarationInformation(final IProgramVar pv) {
		if (pv instanceof HcBodyVar) {
			return new DeclarationInformation(StorageClass.LOCAL, pv.getProcedure());
		} else if (pv instanceof HcHeadVar) {
//			return new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, pv.getProcedure());
			return new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, pv.getProcedure());
		} else {
			throw new AssertionError();
		}
	}

	public String getMethodNameForPredSymbol(final FunctionSymbol function) {
		return function.getName();
	}

	public String getMethodNameForPredSymbol(final HornClausePredicateSymbol predSym) {
		return predSym.getName();
	}

	public List<HcHeadVar> getHcHeadVarsForPredSym(final HornClausePredicateSymbol bodySymbol) {
		final List<HcHeadVar> result = new ArrayList<>();
		for (int i = 0; i < bodySymbol.getArity(); i++) {
			result.add(getHeadVar(bodySymbol.getName(), i, bodySymbol.getParameterSorts().get(i)));
		}
		return result;
	}

}
