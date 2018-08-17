package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayGroup;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain.HeapSepProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class MemlocArrayManager {

	private boolean mIsFrozen;

	public static final String MEMLOC = "##memloc";
	public static final String MEMLOC_SORT_INT = "##mmlc_sort_int";

	final Map<Integer, IProgramNonOldVar> mDimToMemlocArrayInt = new HashMap<>();
	final Map<Integer, Sort> mDimToMemLocSort = new HashMap<>();

	boolean mAlreadyDeclaredMemlocSort;

	private final ManagedScript mMgdScript;

	private Map<IProgramNonOldVar, Term> mMemlocArrayToInitConstArray;

	private Map<IProgramVarOrConst, IProgramConst> mMemlocArrayToLit;

	public MemlocArrayManager(final ManagedScript mgdScript) {
		mMgdScript = mgdScript;
		mIsFrozen = false;
	}

	public IProgramNonOldVar getOrConstructLocArray(final ArrayGroup updatedArray, final int dim) {
		final todo: take updatedArray into final account
		IProgramNonOldVar result = mDimToMemlocArrayInt.get(dim);
		if (result == null) {
			assert !mIsFrozen;
			mMgdScript.lock(this);
			final Sort intToLocations = SmtSortUtils.getArraySort(mMgdScript.getScript(),
					SmtSortUtils.getIntSort(mMgdScript), getMemlocSort(dim));
			result = ProgramVarUtils.constructGlobalProgramVarPair(MEMLOC + "_int_" + dim, intToLocations, mMgdScript,
					this);
			mMgdScript.unlock(this);

			mDimToMemlocArrayInt.put(dim, result);

		}
		return result;
	}

	public Sort getMemlocSort(final int dim) {
		// TODO: should we have a different sort per dimension?
		if (!mAlreadyDeclaredMemlocSort) {
			mMgdScript.getScript().declareSort(MEMLOC_SORT_INT, 0);
			mAlreadyDeclaredMemlocSort = true;
		}
		return mMgdScript.getScript().sort(MEMLOC_SORT_INT);
	}

	public Map<IProgramNonOldVar, Term> getMemlocArrayToInitConstantArray() {
		// this may be called only after all memloc arrays that we need have been created.";

		if (!mIsFrozen){
			mIsFrozen = true;
			mMgdScript.lock(this);

			assert mMemlocArrayToInitConstArray == null;
			mMemlocArrayToInitConstArray = new HashMap<>();
			assert mMemlocArrayToLit == null;
			mMemlocArrayToLit = new HashMap<>();

			for (final Entry<Integer, IProgramNonOldVar> en : mDimToMemlocArrayInt.entrySet()) {
				final Integer dim = en.getKey();
				final IProgramNonOldVar memlocArray = en.getValue();

				// literal has value sort (the sort of the memloc literals), we will create a constant array from it
				final String memlocLitName = getMemlocLitName(memlocArray);
				mMgdScript.declareFun(this, memlocLitName, new Sort[0], getMemlocSort(dim));

				final ApplicationTerm memlocLitTerm = (ApplicationTerm) mMgdScript.term(this, memlocLitName);

				mMemlocArrayToLit.put(memlocArray, new HeapSepProgramConst(memlocLitTerm));

				final Term constArray = mMgdScript.term(this, "const", null, memlocArray.getSort(), memlocLitTerm);
				mMemlocArrayToInitConstArray.put(memlocArray, constArray);
			}
			mMgdScript.unlock(this);
		}
		return mMemlocArrayToInitConstArray;
	}

	private String getMemlocLitName(final IProgramNonOldVar memlocVar) {
		// TODO make _really_ sure that the new id is unique
		return memlocVar.getGloballyUniqueId() + "_lit";
	}

	public Set<IProgramConst> getMemLocLits() {
		return new HashSet<>(mMemlocArrayToLit.values());
	}
}