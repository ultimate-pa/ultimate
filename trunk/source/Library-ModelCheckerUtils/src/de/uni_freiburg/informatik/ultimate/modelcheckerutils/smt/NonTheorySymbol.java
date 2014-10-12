package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Wrapper for non-theory SMT symbols. 
 * A non-theory symbol is either a TermVariable, a constant or a FunctionSymbol.
 * We need this class because there is no common superclass for these three 
 * classes.
 * @author Matthias Heizmann
 *
 */
public class NonTheorySymbol<SYMBOL> {
	private final SYMBOL m_Symbol;

	private NonTheorySymbol(SYMBOL symbol) {
		super();
		m_Symbol = symbol;
	}

	public SYMBOL getSymbol() {
		return m_Symbol;
	}

	@Override
	public final int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((m_Symbol == null) ? 0 : m_Symbol.hashCode());
		return result;
	}

	@Override
	public final boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		NonTheorySymbol other = (NonTheorySymbol) obj;
		if (m_Symbol == null) {
			if (other.m_Symbol != null)
				return false;
		} else if (!m_Symbol.equals(other.m_Symbol))
			return false;
		return true;
	}
	
	
	
	@Override
	public final String toString() {
		return m_Symbol.toString();
	}

	public static Set<NonTheorySymbol<?>> extractNonTheorySymbols(Term term) {
		return (new NonTheorySymbolFinder()).findNonTheorySymbols(term);
	}
	
	public static class Variable extends NonTheorySymbol<TermVariable> {
		public Variable(TermVariable tv) {
			super(tv);
		}
	}
	
	public static class Constant extends NonTheorySymbol<ApplicationTerm> {
		public Constant(ApplicationTerm constant) {
			super(constant);
			if (constant.getParameters().length > 0) {
				throw new IllegalArgumentException("this is no constant");
			}
			if (constant.getFunction().isIntern()) {
				throw new IllegalArgumentException("this is not a non-theory symbol");
			}
		}
	}
	
	public static class Function extends NonTheorySymbol<FunctionSymbol> {
		public Function(FunctionSymbol functionSymbol) {
			super(functionSymbol);
			if (functionSymbol.isIntern()) {
				throw new IllegalArgumentException("this is not a non-theory symbol");
			}
		}
	}
}


