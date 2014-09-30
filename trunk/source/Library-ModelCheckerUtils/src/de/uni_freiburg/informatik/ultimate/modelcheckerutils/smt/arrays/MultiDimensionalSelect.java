package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ApplicationTermFinder;

/**
 * Data structure for a (possibly) array select expression.
 * In the array theory of SMT-LIB the Array sort has only two parameters one
 * for the index and one for the value.
 * We model multidimensional arrays by nesting arrays. E.g. an array with two
 * integer indices and real values has the following Sort. 
 * (Array Int -> (Array Int -> Real))
 * The select function has the following signature. (select (Array X Y) X Y)
 * Hence we have to use nested select expressions for multidimensional array
 * reads, e.g., in order to access the position (i1,i2) of an array we use the
 * following term. ("select" ("select" a i1) i2)
 * This is data structure is a wrapper for such a nested select expression which
 * allows you to directly access the array and the indices.
 * This data structure allows also multidimensional arrays of dimension 0. In
 * this case, m_Array is null, m_Index is empty and m_SelectTerm is some term.
 * @author Matthias Heizmann
 *
 */
public class MultiDimensionalSelect {

	private final Term m_Array;
	private final ArrayIndex m_Index;
	private final ApplicationTerm m_SelectTerm;
	
	/**
	 * Translate a (possibly) nested SMT term into this data structure.
	 * @param term term of the form ("select" a i2) for some array a and some
	 * index i2.
	 */
	public MultiDimensionalSelect(Term term) {
		m_SelectTerm = (ApplicationTerm) term;
		ArrayList<Term> index = new ArrayList<Term>();
		while (true) {
			if (!(term instanceof ApplicationTerm)) {
				break;
			}
			ApplicationTerm appTerm = (ApplicationTerm) term;
			if (!appTerm.getFunction().getName().equals("select")) {
				break;
			}
			assert appTerm.getParameters().length == 2;
			index.add(0,appTerm.getParameters()[1]);
			term = appTerm.getParameters()[0];
		}
		m_Index = new ArrayIndex(index);
		m_Array = term;
		assert classInvariant();
	}
	
	private boolean classInvariant() {
		if (m_Array == null) {
			return m_Index.size() == 0;
		} else {
			return MultiDimensionalSort.
					areDimensionsConsistent(m_Array, m_Index, m_SelectTerm);
		}
	}
	
	public Term getArray() {
		return m_Array;
	}

	public ArrayIndex getIndex() {
		return m_Index;
	}

	public ApplicationTerm getSelectTerm() {
		return m_SelectTerm;
	}
	
	@Override
	public String toString() {
		return m_SelectTerm.toString();
	}
	
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof MultiDimensionalSelect) {
			return m_SelectTerm.equals(((MultiDimensionalSelect) obj).getSelectTerm());
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return m_SelectTerm.hashCode();
	}
	
	
	/**
	 * Return all MultiDimensionalSelect Objects for all multidimensional 
	 * select expressions that occur in term.
	 * If one multidimensional expression occurs in another multidimensional
	 * select expression (e.g. as index) the nested one is not returned by
	 * this method.
	 * If an select term occurs multiple times it is contained multiple times
	 * in the result.
	 * @param allowArrayValues allow also MultiDimensionalSelect terms whose
	 * Sort is an array Sort (these select terms occur usually in 
	 * multidimensional store terms).
	 */
	public static List<MultiDimensionalSelect> extractSelectShallow(
			Term term, boolean allowArrayValues) {
		List<MultiDimensionalSelect> result = new ArrayList<MultiDimensionalSelect>();
		Set<ApplicationTerm> selectTerms = 
				(new ApplicationTermFinder("select", false)).findMatchingSubterms(term);
		for (Term storeTerm : selectTerms) {
			if (allowArrayValues || !storeTerm.getSort().isArraySort()) {
				MultiDimensionalSelect mdSelect = new MultiDimensionalSelect(storeTerm);
				if (mdSelect.getIndex().size() == 0) {
					throw new AssertionError("select must not have dimension 0");
				}
				result.add(mdSelect);
			}
		}
		return result;
	}
	
	/**
	 * Return all MultiDimensionalSelect Objects for all select expressions
	 * that occur in term. This method also return the inner multidimensional
	 * select expressions in other multidimensional select expressions.
	 * If an select term occurs multiple times it is contained multiple times
	 * in the result.
	 * If multidimensional selects are nested, the inner ones occur earlier
	 * in the resulting list.
	 * @param allowArrayValues allow also MultiDimensionalSelect terms whose
	 * Sort is an array Sort (these select terms occur usually in 
	 * multidimensional store terms).
	 */
	public static List<MultiDimensionalSelect> extractSelectDeep(
			Term term, boolean allowArrayValues) {
		List<MultiDimensionalSelect> result = new LinkedList<MultiDimensionalSelect>();
		List<MultiDimensionalSelect> foundInThisIteration = extractSelectShallow(term, allowArrayValues);
		while (!foundInThisIteration.isEmpty()) {
			result.addAll(0, foundInThisIteration);
			List<MultiDimensionalSelect> foundInLastIteration = foundInThisIteration;
			foundInThisIteration = new ArrayList<MultiDimensionalSelect>();
			for (MultiDimensionalSelect mdSelect : foundInLastIteration) {
				foundInThisIteration.addAll(extractSelectShallow(mdSelect.getArray(), allowArrayValues));
				ArrayIndex index = mdSelect.getIndex();
				for (Term entry : index) {
					foundInThisIteration.addAll(extractSelectShallow(entry, allowArrayValues));
				}
			}
		}
		return result;
	}
}