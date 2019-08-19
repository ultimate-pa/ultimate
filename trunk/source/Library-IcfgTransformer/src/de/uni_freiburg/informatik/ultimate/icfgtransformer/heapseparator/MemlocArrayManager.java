package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.EdgeInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.NoStoreInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.StoreInfo;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.HeapSepProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;

public class MemlocArrayManager {

	private boolean mFrozen;

	public static final String LOC_ARRAY_PREFIX = "#loc";
	public static final String LOC_SORT_PREFIX = "#locsort";
	public static final String INITLOCLIT_PREFIX = "#initloclit";

	private final ManagedScript mMgdScript;

	private final Map<Integer, Sort> mDimToLocSort = new HashMap<>();

	private final NestedMap3<EdgeInfo, Term, Integer, LocArrayInfo> mEdgeToArrayTermToDimToLocArray =
			new NestedMap3<>();

	/**
	 * used for internal caching
	 */
	private final NestedMap2<IProgramVarOrConst, Integer, IProgramVarOrConst> mArrayPvocToDimToLocArrayPvoc =
			new NestedMap2<>();

	private final Map<Sort, HeapSepProgramConst> mLocArraySortToInitLocLit = new HashMap<>();

	private final Set<IProgramNonOldVar> mGlobalLocArrays = new HashSet<>();

	private final Map<Term, HeapSepProgramConst> mInitLocLitTermToPvoc = new HashMap<>();

	private final Map<HeapSepProgramConst, NoStoreInfo> mInitLocPvocToNoStoreInfo = new HashMap<>();

	private final ComputeStoreInfosAndArrayGroups<?> mCsiag;

	private int mNoStoreInfoCounter = -1;

	public MemlocArrayManager(final ManagedScript mgdScript,
			final ComputeStoreInfosAndArrayGroups<?> computeStoreInfosAndArrayGroups) {
		mMgdScript = mgdScript;
		mFrozen = false;
		mCsiag = computeStoreInfosAndArrayGroups;
	}

	/**
	 * We have different sorts for different dimensions. Note that it does not make sense to have different sorts for
	 * different arrays (perhaps for differentarray groups..)
	 *
	 * @param dim
	 * @return
	 */
	public Sort getMemlocSort(final int dim) {
		Sort result = mDimToLocSort.get(dim);
		if (result == null) {
			final String name = LOC_SORT_PREFIX + dim;
			mMgdScript.getScript().declareSort(name, 0);
			result = mMgdScript.getScript().sort(name);
			mDimToLocSort.put(dim, result);
		}
		return result;
	}

	public Set<HeapSepProgramConst> getInitLocLits() {
		if (!mFrozen) {
			throw new AssertionError();
		}
		return new HashSet<>(mLocArraySortToInitLocLit.values());
	}

	public LocArrayInfo getOrConstructLocArray(final EdgeInfo edgeInfo, final Term baseArrayTerm, final int dim) {
		return getOrConstructLocArray(edgeInfo, baseArrayTerm, dim, false);
	}

	/**
	 *
	 * @param edgeInfo
	 * @param baseArrayTerm
	 * @param dim
	 * @param calledFromProcessSelect
	 *            not called during preprocessing before abstract interpretation but because of an array read..
	 * @return
	 */
	public LocArrayInfo getOrConstructLocArray(final EdgeInfo edgeInfo, final Term baseArrayTerm, final int dim,
			final boolean calledFromProcessSelect) {
		LocArrayInfo result = mEdgeToArrayTermToDimToLocArray.get(edgeInfo, baseArrayTerm, dim);
		if (result == null) {
			if (calledFromProcessSelect) {
				// called from after-ai querying --> no update to the array should happen in the edge
				final IProgramVarOrConst pvoc = edgeInfo.getProgramVarOrConstForTerm(baseArrayTerm);
				// pvoc should be in an out, with tv baseArrayTerm
				assert edgeInfo.getOutVar(baseArrayTerm) == pvoc;
				assert edgeInfo.getInVar(baseArrayTerm) == pvoc;
				assert !edgeInfo.getEdge().getTransformula().getAssignedVars().contains(pvoc);

				final Sort locArraySort = computeLocArraySort(baseArrayTerm.getSort(), dim);
				mMgdScript.lock(this);
				final IProgramVarOrConst locPvoc = getLocArrayPvocForArrayPvoc(pvoc, dim, locArraySort);
				mMgdScript.unlock(this);

				/*
				 * because there is no update to the array, no LocArray was constructed here during pre-ai-processing
				 * also, the loc-array is not updated, and not read in the ai-preprocessed program, thus, in the
				 * EqualityProvidingIntermediateState, it must be queried via the standard-pvoc-term
				 */
				result = new LocArrayReadInfo(edgeInfo, locPvoc, locPvoc.getTerm());
				mEdgeToArrayTermToDimToLocArray.put(edgeInfo, baseArrayTerm, dim, result);
			} else {
				assert !mFrozen;

				mMgdScript.lock(this);
				final Sort locArraySort = computeLocArraySort(baseArrayTerm.getSort(), dim);

				final IProgramVarOrConst pvoc;
				final Term term;
				{
					if (baseArrayTerm instanceof TermVariable) {
						final IProgramVar invar = edgeInfo.getInVar(baseArrayTerm);
						final IProgramVar outvar = edgeInfo.getOutVar(baseArrayTerm);
						final boolean isAuxVar = edgeInfo.getAuxVars().contains(baseArrayTerm);

						if (invar != null) {
							pvoc = getLocArrayPvocForArrayPvoc(invar, dim, locArraySort);
							term = mMgdScript.constructFreshTermVariable(
									sanitizeVarName(LOC_ARRAY_PREFIX + baseArrayTerm + "_" + dim), locArraySort);
						} else if (outvar != null) {
							pvoc = getLocArrayPvocForArrayPvoc(outvar, dim, locArraySort);
							term = mMgdScript.constructFreshTermVariable(
									sanitizeVarName(LOC_ARRAY_PREFIX + baseArrayTerm + "_" + dim), locArraySort);
						} else if (isAuxVar) {
							pvoc = null;
							term = mMgdScript.constructFreshTermVariable(
									sanitizeVarName(LOC_ARRAY_PREFIX + baseArrayTerm + "_" + dim), locArraySort);
						} else {
							throw new AssertionError();
						}
					} else {
						throw new UnsupportedOperationException("todo: deal with constants");
					}
				}
				final HeapSepProgramConst initLocLit = getOrConstructInitLocLitForLocArraySort(locArraySort, dim);
				result = new LocArrayInfo(edgeInfo, pvoc, term,
						computeInitConstantArrayForLocArray(initLocLit, locArraySort, this));

				mMgdScript.unlock(this);

				mEdgeToArrayTermToDimToLocArray.put(edgeInfo, baseArrayTerm, dim, result);
			}
		}
		return result;
	}

	public Term getInitConstArrayForGlobalLocArray(final IProgramNonOldVar pnov, final Object lockOwner) {
		final Sort locArraySort = pnov.getSort();
		final int dim = new MultiDimensionalSort(locArraySort).getDimension();
		final HeapSepProgramConst initLocLit = getOrConstructInitLocLitForLocArraySort(locArraySort, dim);
		return computeInitConstantArrayForLocArray(initLocLit, locArraySort, lockOwner);
	}

	public Set<IProgramNonOldVar> getGlobalLocArrays() {
		if (!mFrozen) {
			throw new AssertionError();
		}
		return Collections.unmodifiableSet(mGlobalLocArrays);
	}

	private HeapSepProgramConst getOrConstructInitLocLitForLocArraySort(final Sort locArraySort, final int dim) {
		assert new MultiDimensionalSort(locArraySort).getDimension() == dim;
		HeapSepProgramConst result = mLocArraySortToInitLocLit.get(locArraySort);

		if (result == null) {
			assert mMgdScript.isLockOwner(this);
			final String litName = INITLOCLIT_PREFIX + dim;
			mMgdScript.declareFun(this, litName, new Sort[0], getMemlocSort(dim));
			final ApplicationTerm locLitTerm = (ApplicationTerm) mMgdScript.term(this, litName);
			result = new HeapSepProgramConst(locLitTerm);
			mInitLocLitTermToPvoc.put(locLitTerm, result);
			mLocArraySortToInitLocLit.put(locArraySort, result);
			mInitLocPvocToNoStoreInfo.put(result, new NoStoreInfo(mNoStoreInfoCounter--));
		}
		return result;
	}

	private IProgramVarOrConst getLocArrayPvocForArrayPvoc(final IProgramVarOrConst pvoc, final int dim,
			final Sort locArraySort) {
		assert mMgdScript.isLockOwner(this) : "locking before calling this, by convention "
				+ "(unclear if there are compelling arguments for the convention)";
		IProgramVarOrConst result = mArrayPvocToDimToLocArrayPvoc.get(pvoc, dim);
		if (result == null) {
			if (pvoc instanceof IProgramNonOldVar) {
				result = ProgramVarUtils.constructGlobalProgramVarPair(
						sanitizeVarName(LOC_ARRAY_PREFIX + "_" + pvoc + "_" + locArraySort), locArraySort, mMgdScript,
						this);
				mGlobalLocArrays.add((IProgramNonOldVar) result);
			} else if (pvoc instanceof ILocalProgramVar) {
				result = ProgramVarUtils.constructLocalProgramVar(
						sanitizeVarName(LOC_ARRAY_PREFIX + "_" + pvoc + "_" + locArraySort),
						((ILocalProgramVar) pvoc).getProcedure(), locArraySort, mMgdScript, this);
			} else if (pvoc instanceof IProgramConst) {
				throw new UnsupportedOperationException("todo: deal with constants");
			} else {
				throw new AssertionError("unforseen case");
			}
			mArrayPvocToDimToLocArrayPvoc.put(pvoc, dim, result);
		}
		return result;
	}

	private String sanitizeVarName(final String string) {
		final String result = string.replaceAll("\\|", "").replaceAll("\\ ", "-");
		if (result.isEmpty()) {
			throw new AssertionError();
		}
		return result;
	}

	/**
	 * Replace the last entry in the given array sort by the loc array sort. Also account for the given dimension by
	 * dropping the innermost dimensions. (e.g. if sort is Int x Real -> Int, and dim is 1, then construct the sort Int
	 * -> locsort1
	 *
	 *
	 * @param sort
	 * @param dim
	 * @return
	 */
	private Sort computeLocArraySort(final Sort sort, final int dim) {
		final MultiDimensionalSort mds = new MultiDimensionalSort(sort);
		assert mds.getDimension() > 0;
		final Deque<Sort> sortDeque = new ArrayDeque<>(mds.getIndexSorts());

		// drop 'innermost' sorts so #dim sorts remain
		for (int i = 0; i < mds.getDimension() - dim; i++) {
			sortDeque.pollLast();
		}
		assert sortDeque.size() == dim;

		// Sort resultSort = getMemlocSort(mds.getDimension());
		Sort resultSort = getMemlocSort(dim);

		while (!sortDeque.isEmpty()) {
			final Sort last = sortDeque.pollLast();
			resultSort = SmtSortUtils.getArraySort(mMgdScript.getScript(), last, resultSort);
		}
		return resultSort;
	}

	private Term computeInitConstantArrayForLocArray(final HeapSepProgramConst locLit, final Sort locArraySort,
			final Object lockOwner) {
		final MultiDimensionalSort mds = new MultiDimensionalSort(locArraySort);
		if (mds.getDimension() == 1) {
			return mMgdScript.term(lockOwner, "const", null, locArraySort, locLit.getTerm());
		} else {
			assert !locArraySort.getArguments()[0].isArraySort();
			final Term inner = computeInitConstantArrayForLocArray(locLit, locArraySort.getArguments()[1], lockOwner);
			return mMgdScript.term(lockOwner, "const", null, locArraySort, inner);
		}
	}

	public LocArrayInfo getLocArray(final EdgeInfo edgeInfo, final Term array, final int dim) {
		if (!mFrozen) {
			throw new AssertionError();
		}
		final LocArrayInfo result = mEdgeToArrayTermToDimToLocArray.get(edgeInfo, array, dim);
		if (result == null) {
			throw new IllegalArgumentException();
		}
		return result;
	}

	public HeapSepProgramConst getInitLocLitPvocForLocLitTerm(final Term locLitTerm) {
		return mInitLocLitTermToPvoc.get(locLitTerm);
	}

	public boolean isInitLocPvoc(final HeapSepProgramConst hspc) {
		final boolean result = mInitLocPvocToNoStoreInfo.containsKey(hspc);
		assert result == mInitLocLitTermToPvoc.values().contains(hspc);
		return result;
	}

	public StoreInfo getNoStoreInfo(final HeapSepProgramConst hspc) {
		return mInitLocPvocToNoStoreInfo.get(hspc);
	}

	public void freeze() {
		if (mFrozen) {
			throw new AssertionError();
		}
		mFrozen = true;
	}

	public boolean isArrayTermSubjectToSeparation(final EdgeInfo edge, final Term bat) {
		return mCsiag.isArrayTermSubjectToSeparation(edge, bat);
	}
}