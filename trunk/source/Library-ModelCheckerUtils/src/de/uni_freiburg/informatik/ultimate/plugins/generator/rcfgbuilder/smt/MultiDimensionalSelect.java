package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Data structure for a (possibly) array select expression.
 * In the array theory of SMT-LIB the Array sort has only two parameters one
 * for the index and one for the value.
 * We model multi-dimensional arrays by nesting arrays. E.g. an array with tow
 * integer indices and real values has the following Sort. 
 * (Array Int -> (Array Int -> Real))
 * The select function has the following signature. (select (Array X Y) X Y)
 * Hence we have to use nested select expressions for multi-dimensional array
 * reads, e.g., ("select" ("select" a i1) i2)
 * This is data structure represents such a nested select expression in which
 * you can directly access all indices and the array.
 *
 */
public class MultiDimensionalSelect {


	private final Term m_Array;
	private final Term[] m_Index;
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
		m_Index = index.toArray(new Term[0]);
		m_Array = term;
		if (index.isEmpty()) {
			throw new AssertionError("select of dimension 0 unsupported");
		}
		assert areDimensionsConsistent(m_Index, m_Array, m_SelectTerm);
//		int dimensionArray = ElimStore3.getDimension(term.getSort());
//		int numberOfIndices = m_Index.length;
//		int dimensionResult = ElimStore3.getDimension(m_SelectTerm.getSort());
//		assert (numberOfIndices == dimensionArray - dimensionResult);
	}
	
	private boolean areDimensionsConsistent(Term[] index, Term array,
			ApplicationTerm selectTerm) {
		int dimensionArray = (new SmtUtils.MultiDimensionalArraySort(
				array.getSort())).getDimension();
		int dimensionSelect = (new SmtUtils.MultiDimensionalArraySort(
				selectTerm.getSort())).getDimension();
		return (index.length == dimensionArray - dimensionSelect);
	}

	public Term getArray() {
		return m_Array;
	}

	public Term[] getIndex() {
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
	 * Return all MultiDimensionalSelect Objects for all multi-dimensional 
	 * select expressions that occur in term.
	 * If one multi-dimensional expression occurs in another multi-dimensional
	 * select expression (e.g. as index) the nested one is not returned by
	 * this method.
	 * If an select term occurs multiple times it is contained multiple times
	 * in the result.
	 * @param allowArrayValues allow also MultiDimensionalSelect terms whose
	 * Sort is an array Sort (these select terms occur usually in 
	 * multi-dimensional store terms).
	 */
	public static List<MultiDimensionalSelect> extractSelectShallow(
			Term term, boolean allowArrayValues) {
		List<MultiDimensionalSelect> result = new ArrayList<MultiDimensionalSelect>();
		Set<ApplicationTerm> selectTerms = 
				(new ApplicationTermFinder("select", false)).findMatchingSubterms(term);
		for (Term storeTerm : selectTerms) {
			if (allowArrayValues || !storeTerm.getSort().isArraySort()) {
				MultiDimensionalSelect mdSelect = new MultiDimensionalSelect(storeTerm);
				result.add(mdSelect);
			}
		}
		return result;
	}
	
	/**
	 * Return all MultiDimensionalSelect Objects for all select expressions
	 * that occur in term. This method also return the inner multi-dimensional
	 * select expressions in other multi-dimensional select expressions.
	 * If an select term occurs multiple times it is contained multiple times
	 * in the result.
	 * If multi-dimensional selects are nested, the inner ones occur earlier
	 * in the resulting list.
	 * @param allowArrayValues allow also MultiDimensionalSelect terms whose
	 * Sort is an array Sort (these select terms occur usually in 
	 * multi-dimensional store terms).
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
				Term[] index = mdSelect.getIndex();
				for (Term entry : index) {
					foundInThisIteration.addAll(extractSelectShallow(entry, allowArrayValues));
				}
			}
		}
		return result;
	}
}