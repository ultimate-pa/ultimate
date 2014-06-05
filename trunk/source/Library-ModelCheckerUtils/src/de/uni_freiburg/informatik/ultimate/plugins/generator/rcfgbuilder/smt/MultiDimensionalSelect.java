package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Given a (possibly nested) array a, this is a data structure for terms of
 * the form  (select (select a i1) i2)  
 *
 */
public class MultiDimensionalSelect {


	private final Term m_Array;
	private final Term[] m_Index;
	private final ApplicationTerm m_SelectTerm;
	
	
	
	public MultiDimensionalSelect(Term term, Term array) throws MultiDimensionalSelect.ArrayReadException {
		if (!(term instanceof ApplicationTerm)) {
			throw new MultiDimensionalSelect.ArrayReadException(false, "no ApplicationTerm");
		}
		m_SelectTerm = (ApplicationTerm) term;
		int dimensionArray = ElimStore3.getDimension(array.getSort());
		int dimensionResult = ElimStore3.getDimension(m_SelectTerm.getSort());
		int numberOfIndices = dimensionArray - dimensionResult;
		m_Index = new Term[numberOfIndices];			
		for (int i = numberOfIndices-1; i>=0; i--) {
			if (!(term instanceof ApplicationTerm)) {
				throw new MultiDimensionalSelect.ArrayReadException(false, "no ApplicationTerm");
			}
			ApplicationTerm appTerm = (ApplicationTerm) term;
			if (!appTerm.getFunction().getName().equals("select")) {
				throw new MultiDimensionalSelect.ArrayReadException(false, "no select");
			}
			assert appTerm.getParameters().length == 2;
			m_Index[i] = appTerm.getParameters()[1];
			term = appTerm.getParameters()[0];
		}
		if (!array.equals(term)) {
			throw new MultiDimensionalSelect.ArrayReadException(true, "different array");
		} else  {
			m_Array = array;
		}
	}
	
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
			throw new AssertionError("krasserer fehler");
		}
		int dimensionArray = ElimStore3.getDimension(term.getSort());
		int numberOfIndices = m_Index.length;
		int dimensionResult = ElimStore3.getDimension(m_SelectTerm.getSort());
		assert (numberOfIndices == dimensionArray - dimensionResult);
	}
	
	private boolean isArray(Term term) {
		if (!term.getSort().isArraySort()) {
			return false;
		}
		if (term instanceof TermVariable) {
			return true;
		}
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			if (appTerm.getParameters().length == 0) {
				// is a constant that represents array
			}
		}
		return false;
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
	
	
	public static class ArrayReadException extends Exception {
		
		private static final long serialVersionUID = -628021699371967800L;
		private final boolean m_DifferentArray;
	
		public ArrayReadException(boolean differentArray, String message) {
			super(message);
			m_DifferentArray = differentArray;
		}

	}
}