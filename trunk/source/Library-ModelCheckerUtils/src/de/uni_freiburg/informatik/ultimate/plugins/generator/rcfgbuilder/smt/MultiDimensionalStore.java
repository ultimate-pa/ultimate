package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Given a (possibly nested) array a, this is a data structure for terms of
 * the form  (select (select a i1) i2)  
 *
 */
public class MultiDimensionalStore {
	private Term m_Array;
	private final Term[] m_Index;
	private final Term m_Data;
	private final ApplicationTerm m_StoreTerm;
	
	public MultiDimensionalStore(Term term) throws MultiDimensionalStore.ArrayStoreException {
		if (!term.getSort().isArraySort()) {
			throw new MultiDimensionalStore.ArrayStoreException(false, "no Array");
		}
		if (!(term instanceof ApplicationTerm)) {
			throw new MultiDimensionalStore.ArrayStoreException(false, "no ApplicationTerm");
		}
		m_StoreTerm = (ApplicationTerm) term;
		int dimension = ElimStore3.getDimension(term.getSort());
		m_Index = new Term[dimension];			
		for (int i=0; i<dimension; i++) {
			if (!(term instanceof ApplicationTerm)) {
				throw new MultiDimensionalStore.ArrayStoreException(false, "no ApplicationTerm");
			}
			ApplicationTerm appTerm = (ApplicationTerm) term;
			if (!appTerm.getFunction().getName().equals("store")) {
				throw new MultiDimensionalStore.ArrayStoreException(false, "no store");
			}
			assert appTerm.getParameters().length == 3;
			if (i == 0) {
				m_Array = appTerm.getParameters()[0];
				assert m_Array.getSort() == m_StoreTerm.getSort();
			} else {
				assert checkSelect(i, appTerm.getParameters()[0]);
			}
			m_Index[i] = appTerm.getParameters()[1];
			term = appTerm.getParameters()[2];
		}
		m_Data = term;
	}
	
	private boolean checkSelect(int i, Term select) {
		boolean result = true;
		MultiDimensionalSelect ar = new MultiDimensionalSelect(select);
		result &= ar.getArray().equals(m_Array);
		for (int j=0; j<i; j++) {
			result &= ar.getIndex()[j] == m_Index[j];
		}
		return result;
	}
	
	
	
	public Term getArray() {
		return m_Array;
	}

	public Term[] getIndex() {
		return m_Index;
	}

	public Term getData() {
		return m_Data;
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
	
	public static class ArrayStoreException extends Exception {
	
	private static final long serialVersionUID = -628021699371967800L;
	private final boolean m_DifferentArray;

	public ArrayStoreException(boolean differentArray, String message) {
		super(message);
		m_DifferentArray = differentArray;
	}
}
	
	
}