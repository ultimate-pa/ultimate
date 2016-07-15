package de.uni_freiburg.informatik.ultimate.lassoranker.mapelimination;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;

/**
 * This class represents an array-write (built from a Term)
 * <p>
 * Given a term like
 * <p>
 * {@code (= b (store (... (store a i_1 x_1) ...) i_n x_n))}
 * <p>
 * {@code a} is the old array and {@code b} the new array (n might be also zero!) and the stores are in the store list
 * <p>
 * For a term like
 * <p>
 * {@code (store (... (store a i_1 x_1) ...) i_n x_n)} analog, but new array is {@code null} then
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class ArrayWrite {

	private final Term mOldArray;
	private Term mNewArray = null;
	private final List<MultiDimensionalStore> mStoreList = new ArrayList<>();

	public ArrayWrite(final Term term) {
		Term arrayTerm;
		if (SmtUtils.isFunctionApplication(term, "=")) {
			final ApplicationTerm a = (ApplicationTerm) term;
			final Term a1 = a.getParameters()[0];
			final Term a2 = a.getParameters()[1];
			if (SmtUtils.isFunctionApplication(a1, "store")) {
				mNewArray = a2;
				arrayTerm = a1;
			} else {
				mNewArray = a1;
				arrayTerm = a2;
			}
		} else {
			arrayTerm = term;
		}
		while (SmtUtils.isFunctionApplication(arrayTerm, "store")) {
			final MultiDimensionalStore store = new MultiDimensionalStore(arrayTerm);
			mStoreList.add(store);
			arrayTerm = store.getArray();
		}
		mOldArray = arrayTerm;
	}

	public Term getOldArray() {
		return mOldArray;
	}

	public Term getNewArray() {
		return mNewArray;
	}

	public List<MultiDimensionalStore> getStoreList() {
		return mStoreList;
	}
}
