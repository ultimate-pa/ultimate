package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ApplicationTermFinder;

/**
 * Data structure for a (possibly) nested array select expression.
 * In the array theory of SMT-LIB the Array sort has only two parameters one
 * for the index and one for the value.
 * We model multidimensional arrays by nesting arrays. E.g. an array with two
 * integer indices and real values has the following Sort. 
 * (Array Int -> (Array Int -> Real))
 * The store function has the following signature. 
 * (store (Array X Y) X Y (Array X Y))
 * Hence we have to use nested store expressions for multidimensional array
 * reads, e.g., in order to get the array that differs from array a only 
 * because at index (i1,i2) the value of v was stored we use the following
 * expression.
 * (store a i1 (store (select a i1) i2 v)) 
 * This is data structure is a wrapper for such a nested select expression which
 * allows you to directly access the array, the indices and the value.
 * This data structure allows also multidimensional arrays of dimension 0. In
 * this case, m_Array is null, m_Index is empty and m_Value coincides with
 * m_StoreTerm.
 * @author Matthias Heizmann
 */
public class MultiDimensionalStore {
	private Term m_Array;
	private final Term[] m_Index;
	private final Term m_Value;
	private final ApplicationTerm m_StoreTerm;
	
	public MultiDimensionalStore(Term term) {
		m_StoreTerm = (ApplicationTerm) term;
		Term array = null;
		ArrayList<Term> index = new ArrayList<Term>();
		Term value = term;
		while (true) {
			if (!(value instanceof ApplicationTerm)) {
				break;
			}
			ApplicationTerm appTerm = (ApplicationTerm) value;
			if (!appTerm.getFunction().getName().equals("store")) {
				break;
			}
			assert appTerm.getParameters().length == 3;
			if (array == null) {
				array = appTerm.getParameters()[0];
			} else {
				assert isCompatibleSelect(appTerm.getParameters()[0], array, index);
			}
			index.add(appTerm.getParameters()[1]);
			value = appTerm.getParameters()[2];
		}
		m_Array = array;
		m_Index = index.toArray(new Term[0]);
		m_Value = value;
		assert classInvariant();
	}
	
	private boolean classInvariant() {
		if (m_Array == null) {
			return m_Index.length == 0 && m_StoreTerm == m_Value;
		} else {
			return m_Array.getSort() == m_StoreTerm.getSort() &&
					MultiDimensionalSort.
					areDimensionsConsistent(m_Array, m_Index, m_Value);
		}
	}
	
	private boolean isCompatibleSelect(Term term, Term array, ArrayList<Term> index) {
		MultiDimensionalSelect mdSelect = new MultiDimensionalSelect(term);
		return mdSelect.getArray() == array && index.equals(Arrays.asList(mdSelect.getIndex()));
	}

	public Term getArray() {
		return m_Array;
	}

	public Term[] getIndex() {
		return m_Index;
	}

	public Term getValue() {
		return m_Value;
	}

	public ApplicationTerm getStoreTerm() {
		return m_StoreTerm;
	}

	@Override
	public String toString() {
		return m_StoreTerm.toString();
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof MultiDimensionalStore) {
			return m_StoreTerm.equals(((MultiDimensionalStore) obj).getStoreTerm());
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return m_StoreTerm.hashCode();
	}
	
	
	/**
	 * Return all MultiDimensionalStore objects for all multidimensional 
	 * store expressions that occur in term.
	 * If one multidimensional store occurs in another multidimensional
	 * store expression (e.g. as index) the nested one is not returned by
	 * this method.
	 * If a store term occurs multiple times it is contained multiple times
	 * in the result.
	 */
	public static List<MultiDimensionalStore> extractArrayStoresShallow(Term term) {
		List<MultiDimensionalStore> arrayStoreDefs = new ArrayList<MultiDimensionalStore>();
		Set<ApplicationTerm> storeTerms = 
				(new ApplicationTermFinder("store", false)).findMatchingSubterms(term);
		for (Term storeTerm : storeTerms) {
			MultiDimensionalStore mdStore = new MultiDimensionalStore(storeTerm);
			if (mdStore.getIndex().length == 0) {
				throw new AssertionError("store must not have dimension 0");
			}
			arrayStoreDefs.add(mdStore);
		}
		return arrayStoreDefs;
	}
	
	
	/**
	 * Return all MultiDimensionalStore objects for all store expressions
	 * that occur in term. This method also return the inner multidimensional
	 * store expressions in other multidimensional store expressions.
	 * If a store term occurs multiple times it is contained multiple times
	 * in the result.
	 * If multidimensional stores are nested, the inner ones occur earlier
	 * in the resulting list.
	 */
	public static List<MultiDimensionalStore> extractArrayStoresDeep(Term term) {
		List<MultiDimensionalStore> result = new LinkedList<MultiDimensionalStore>();
		List<MultiDimensionalStore> foundInThisIteration = extractArrayStoresShallow(term);
		while (!foundInThisIteration.isEmpty()) {
			result.addAll(0, foundInThisIteration);
			List<MultiDimensionalStore> foundInLastIteration = foundInThisIteration;
			foundInThisIteration = new ArrayList<MultiDimensionalStore>();
			for (MultiDimensionalStore asd : foundInLastIteration) {
				foundInThisIteration.addAll(extractArrayStoresShallow(asd.getArray()));
				foundInThisIteration.addAll(extractArrayStoresShallow(asd.getValue()));
				Term[] index = asd.getIndex();
				for (Term entry : index) {
					foundInThisIteration.addAll(extractArrayStoresShallow(entry));
				}
			}
		}
		return result;
	}
	
}