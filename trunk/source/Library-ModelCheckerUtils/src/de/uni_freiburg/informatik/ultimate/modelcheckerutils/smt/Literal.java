package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Represents a boolean term where we explicitly store if the term is negated
 * or not. {@link http://en.wikipedia.org/wiki/Literal_%28mathematical_logic%29}
 * This data structure representa a term φ as a pair (φ_atom, plrty) where
 * atom is a Boolean term and plrty has either the value POSITIVE or NEGATIVE.
 * The pair (φ_atom, POSITIVE) represents the term φ_atom.
 * the pair (φ_atom, NEGATIVE) represents the term (not φ_atom).
 * We call φ_atom the atom of this literal.
 * We call plrty the polarity of this literal.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class Literal {
	
	public enum Polarity { POSITIVE, NEGATIVE };
	private final Term m_Atom;
	private final Polarity m_Polarity;
	
	/**
	 * Convert a Boolean term into this representation. If the input Term is
	 * negated several times, we strip all negation symbols. 
	 */
	public Literal(Term input) {
		super();
		if (!input.getSort().getName().equals("Bool")) {
			throw new IllegalArgumentException("only applicable to sort Bool");
		}
		Term withoutNegation = null;
		int removedNegationSymbols = 0;
		do {
			withoutNegation = getParameterOfNotTerm(input);
			if (withoutNegation != null) {
				input = withoutNegation;
				removedNegationSymbols++;
			}
			
		} while (withoutNegation != null);
		if (removedNegationSymbols % 2 == 0) {
			m_Polarity = Polarity.POSITIVE;
		} else {
			m_Polarity = Polarity.NEGATIVE;
		}
		m_Atom = input;
	}
	
	public Term getAtom() {
		return m_Atom;
	}

	public Polarity getPolarity() {
		return m_Polarity;
	}
	
	public Term toTerm(Script script) {
		if (m_Polarity == Polarity.POSITIVE) {
			return m_Atom;
		} else {
			return script.term("not", m_Atom);
		}
	}


	/**
	 * If term is a negation, i.e. of the form "(not φ)" return the argument
	 * of the negation φ, otherwise return null.
	 */
	public static Term getParameterOfNotTerm(Term term) {
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			if (appTerm.getFunction().getName().equals("not")) {
				assert appTerm.getParameters().length == 1;
				return appTerm.getParameters()[0];
			}
		}
		return null;
	}

}