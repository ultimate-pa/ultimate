package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.mapelimination;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalNestedStore;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * This class represents an array-write (built from a Term)
 * <p>
 * Given a term like
 * <p>
 * {@code (= b (store (... (store a i_1 x_1) ...) i_n x_n))}
 * <p>
 * {@code a} is the old array and {@code b} the new array (n might be also zero!) and the write accesses are in the
 * index-value pairs
 * <p>
 * For a term like
 * <p>
 * {@code (store (... (store a i_1 x_1) ...) i_n x_n)} analog, but new array is {@code null} then
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class ArrayWrite {
	private final Term mOldArray;
	private Term mNewArray;
	private final List<Pair<ArrayIndex, Term>> mIndexValuePairs = new ArrayList<>();

	/**
	 * Creates an ArrayWrite-object from a given term. The term has to be either an array-equality or a store-term.
	 */
	public ArrayWrite(final Term term, final Script script) {
		Term arrayTerm;
		if (SmtUtils.isFunctionApplication(term, "=")) {
			final ApplicationTerm applicationTerm = (ApplicationTerm) term;
			final Term term1 = applicationTerm.getParameters()[0];
			final Term term2 = applicationTerm.getParameters()[1];
			if (SmtUtils.isFunctionApplication(term1, "store")) {
				mNewArray = term2;
				arrayTerm = term1;
			} else {
				mNewArray = term1;
				arrayTerm = term2;
			}
		} else {
			arrayTerm = term;
		}
		final MultiDimensionalNestedStore mdns = MultiDimensionalNestedStore.of(arrayTerm);
		if (mdns == null) {
			mOldArray = arrayTerm;
		} else {
			final List<ArrayIndex> indices = mdns.getIndices();
			final List<Term> values = mdns.getValues();
			for (int i = indices.size() - 1; i >= 0; i--) {
				mIndexValuePairs.add(new Pair<>(indices.get(i), values.get(i)));
			}
			mOldArray = mdns.getArray();
		}
	}

	/**
	 * Returns the old array of an ArrayWrite-object, e.g. for the term {@code (= b (store a i x))} this returns a.
	 */
	public Term getOldArray() {
		return mOldArray;
	}

	/**
	 * Returns the new array of an ArrayWrite-object, e.g. for the term {@code (= b (store a i x))} this returns b, but
	 * for the term {@code (store a i x)} this returns {@code null}.
	 */
	public Term getNewArray() {
		return mNewArray;
	}

	/**
	 * Returns the indices and values written to as a list in descending priority, e.g. for the term
	 * {@code (= b (store (... (store a i_1 x_1) ...) i_n x_n))} this method returns: [(i_n, x_n), ..., (i_1), (x_1)]
	 */
	public List<Pair<ArrayIndex, Term>> getIndexValuePairs() {
		return mIndexValuePairs;
	}
}
