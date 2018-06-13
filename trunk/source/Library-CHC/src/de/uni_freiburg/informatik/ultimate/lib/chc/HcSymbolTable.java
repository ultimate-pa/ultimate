package de.uni_freiburg.informatik.ultimate.lib.chc;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol.HornClauseDontCarePredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol.HornClauseTruePredicateSymbol;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ITerm2ExpressionSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Stores runtime information concerning a set of constrained HornClauses centrally.
 * E.g. to pass information from a parser of a Horn clause format to a plugin like {@link TreeAutomizer} or
 * {@link ChcToBooge} this could be used.
 *
 * FIXME: it is rather questionable if this should be called a symbol table. Right now it only inherits from
 *  {@link DefaultIcfgSymbolTable} in order to not break {@link TreeAutomizer} ever further.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class HcSymbolTable extends DefaultIcfgSymbolTable implements ITerm2ExpressionSymbolTable {

	private final ManagedScript mManagedScript;

	private final NestedMap2<String, List<Sort>, HcPredicateSymbol> mNameToSortsToHornClausePredicateSymbol;

	private HornClauseTruePredicateSymbol mTrueHornClausePredSym;
	private HornClauseDontCarePredicateSymbol mDontCareHornClausePredSym;
	private final HcPredicateSymbol mFalseHornClausePredSym;

	final Map<TermVariable, Integer> mVersionsMap;

	private final NestedMap3<HcPredicateSymbol, Integer, Sort, HcHeadVar> mPredSymNameToIndexToSortToHcHeadVar;
	private final NestedMap3<HcPredicateSymbol, Integer, Sort, HcBodyVar> mPredSymNameToIndexToSortToHcBodyVar;

	private final Map<TermVariable, IProgramVar> mTermVarToProgramVar;

	private final TermTransferrer mTermTransferrer;

	private final Map<String, String> mSmtFunction2BoogieFunction;

	private final HashRelation3<String, Sort[], Sort> mSkolemFunctions;


	/**
	 *
	 * @param mgdScript note, this is the solver, not the parser, as a convention every Term that is saved in this
	 *  symbol table (directly or inside an object) should be transferred to this script.
	 */
	public HcSymbolTable(final ManagedScript mgdScript) {
		super();
		mNameToSortsToHornClausePredicateSymbol = new NestedMap2<>();
		mManagedScript = mgdScript;

		mManagedScript.lock(this);
		{
			final ApplicationTerm bot = (ApplicationTerm) mgdScript.getScript().term("false");
			mFalseHornClausePredSym = new HcPredicateSymbol.HornClauseFalsePredicateSymbol(bot.getFunction());

			final ApplicationTerm top = (ApplicationTerm) mgdScript.getScript().term("true");
			mTrueHornClausePredSym = new HcPredicateSymbol.HornClauseTruePredicateSymbol(top.getFunction());

			mDontCareHornClausePredSym = new HcPredicateSymbol.HornClauseDontCarePredicateSymbol();
		}
		mManagedScript.unlock(this);

		mVersionsMap = new HashMap<>();
		mPredSymNameToIndexToSortToHcHeadVar = new NestedMap3<>();
		mPredSymNameToIndexToSortToHcBodyVar = new NestedMap3<>();
		mTermVarToProgramVar = new HashMap<>();
		mSmtFunction2BoogieFunction = new HashMap<>();
		mSkolemFunctions = new HashRelation3<>();

		mTermTransferrer = new TermTransferrer(mgdScript.getScript());
	}

	public TermVariable createFreshVersion(final TermVariable var) {
		int ver = 1;
		if (mVersionsMap.containsKey(var)) {
			ver = mVersionsMap.get(var) + 1;
		}
		return mManagedScript.constructFreshTermVariable(var.getName() + ver, var.getSort());
	}

	public HcPredicateSymbol getOrConstructHornClausePredicateSymbol(
			final ApplicationTerm at) {
		final ApplicationTerm atTransferred = (ApplicationTerm) mTermTransferrer.transform(at);
		final FunctionSymbol fsym = atTransferred.getFunction();

		final String functionName = fsym.getName();
		final Sort[] functionParamenterSorts = fsym.getParameterSorts();
		final List<Sort> convertedFunctionParamenterSorts = Arrays.asList(functionParamenterSorts);//Arrays.asList(transferSorts(functionParamenterSorts));

		HcPredicateSymbol result = mNameToSortsToHornClausePredicateSymbol.get(
				functionName,
				convertedFunctionParamenterSorts);
		if (result == null) {
			result = new HcPredicateSymbol(this, fsym);
			mNameToSortsToHornClausePredicateSymbol.put(functionName, convertedFunctionParamenterSorts, result);

		}
		return result;
	}

	public HcPredicateSymbol getFalseHornClausePredicateSymbol() {
		return mFalseHornClausePredSym;
	}

	public HcPredicateSymbol getTrueHornClausePredicateSymbol() {
		return mTrueHornClausePredSym;
	}

	public HcPredicateSymbol getDontCareHornClausePredicateSymbol() {
		return mDontCareHornClausePredSym;
	}

	/**
	 * Returns all uninterpreted predicates that are registered in this symbol table.
	 * @return
	 */
	public List<HcPredicateSymbol> getHcPredicateSymbols() {
		return mNameToSortsToHornClausePredicateSymbol.values().collect(Collectors.toList());
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
	public HcHeadVar getHeadVar(final HcPredicateSymbol predSymName, final int index, final Sort sort) {
		final Sort transferredSort = transferSort(sort);
		final HcHeadVar result = mPredSymNameToIndexToSortToHcHeadVar.get(predSymName, index, transferredSort);
		assert result != null;
		return result;
	}

	public HcHeadVar getOrConstructHeadVar(final HcPredicateSymbol predSymName, final int index, final Sort sort) {
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

	public HcBodyVar getOrConstructBodyVar(final HcPredicateSymbol predSymName, final int index, final Sort sort) {
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



//	/**
//	 * Every TermVariable that appears in a HornClause has a default constant associated with it, which is declared
//	 * up front. (used for hoare triple checks)
//	 * @param fv
//	 * @return
//	 */
//	public Term getConstForTermVar(final TermVariable fv) {
//		final ApplicationTerm res = mTermVarToConst.get(fv);
//		assert res != null;
//		return res;
//	}

//	public boolean hasConstForTermVar(final TermVariable fv) {
//		return mTermVarToConst.containsKey(fv);
//	}

//	public HcBodyVar getHCOutVar(final int i, final Sort sort) {
//		final HcBodyVar result = mArgPosToSortToHcOutVar.get(i, sort);
//		if (result == null) {
//			throw new AssertionError();
//		}
//		return result;
//	}

//	public String getHeadVarName(final int i, final Sort sort) {
//		return "headvar_" + i + "_" + sort.getName();
//	}

	@Override
	public BoogieConst getProgramConst(final ApplicationTerm term) {
		throw new AssertionError();
	}

	@Override
	public Map<String, String> getSmtFunction2BoogieFunction() {
		return mSmtFunction2BoogieFunction;
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

	public String getMethodNameForPredSymbol(final HcPredicateSymbol predSym) {
		return HornUtilConstants.sanitzePredName(predSym.getName());
	}

	public List<HcHeadVar> getHcHeadVarsForPredSym(final HcPredicateSymbol bodySymbol,
			final boolean constructIfNecessary) {
		final List<HcHeadVar> result = new ArrayList<>();
		for (int i = 0; i < bodySymbol.getArity(); i++) {
			final HcHeadVar hv = constructIfNecessary ?
					getOrConstructHeadVar(bodySymbol, i, bodySymbol.getParameterSorts().get(i)) :
						getHeadVar(bodySymbol, i, bodySymbol.getParameterSorts().get(i));
			result.add(hv);
		}
		return result;
	}

	public void announceSkolemFunctions(final HashRelation3<String, Sort[], Sort> skolemFunctions) {
		for (final Triple<String, Sort[], Sort> sf : skolemFunctions) {
			assert !mSmtFunction2BoogieFunction.containsKey(sf.getFirst()) : "name clash";
			mSkolemFunctions.addTriple(sf.getFirst(), transferSorts(sf.getSecond()), transferSort(sf.getThird()));
			mSmtFunction2BoogieFunction.put(sf.getFirst(), sf.getFirst());
		}
	}

	public HashRelation3<String, Sort[], Sort> getSkolemFunctions() {
		return mSkolemFunctions;
	}
}
