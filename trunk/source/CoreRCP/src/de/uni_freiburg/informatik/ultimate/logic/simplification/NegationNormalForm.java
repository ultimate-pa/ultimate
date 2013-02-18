package de.uni_freiburg.informatik.ultimate.logic.simplification;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Class to get the negation normal form of a term.
 * Every term which is neither conjunction, disjunction or implication
 * is treated as a literal.
 */
public class NegationNormalForm {
	
	private final Script m_Script;
	
	public NegationNormalForm (final Script script) {
		m_Script = script;
	}
	
	/**
	 * @term term whose Sort is Bool
	 * @return Copy of term that is transformed to negation normal form. Terms
	 *  which are neither conjunction, disjunction or implication is treated as
	 *  a literal.
	 */
	public Term getNNF(Term term) throws SMTLIBException {
		term = (new FormulaUnLet()).unlet(term);
		return this.getNNF(term, false);
	}
	
	
	/**
	 * Calls getNNF for every term in the array separately.
	 * @param change 
	 *       used to remember, if there was a negation, false means no.
	 */
	private Term[] getNNF(final Term[] terms, boolean change)
														throws SMTLIBException {
		Term[] newTerms = new Term[terms.length];
		for (int i = 0; i < terms.length; i++) {
			newTerms[i] = getNNF(terms[i], change);
		}
		return newTerms;
	}
	
	/**
	 * Transforms the term into its negation normal form.
	 * Every term which is neither conjunction, disjunction or implication
	 * is treated as a literal.
	 * @param change 
	 *      used to remember, if there was a negation, false means no.
	 */
	private Term getNNF(final Term term, boolean change) throws SMTLIBException {
		if (term instanceof ApplicationTerm) {
			ApplicationTerm castedTerm =  (ApplicationTerm) term;
			final String castedTermsFunctionName = 
											castedTerm.getFunction().getName();
			// if the function is a negation, change the "change" bool,
			// and go on with its argument.
			if (castedTermsFunctionName.equals("not")) {
				if (change) {
					change = false;
					Term[] para = castedTerm.getParameters();
					return this.getNNF(para[0], change);
				}
				else {
					change = true;
					Term[] para = castedTerm.getParameters();
					return this.getNNF(para[0], change);
				}
			}
			// If the function is a conjunction and there was a negation,
			// flip the function to a disjunction, otherwise let it unchanged
			if (castedTermsFunctionName.equals("and")) {
				if (change) {
					Term[] para = castedTerm.getParameters();
					Term[] newPara = this.getNNF(para, change);
					return m_Script.term("or", newPara);
				}
				else {
					Term[] para = castedTerm.getParameters();
					Term[] newPara = this.getNNF(para, change);
					return m_Script.term("and", newPara);
				}
			}
			// If the function is a disjunction and there was a negation,
			// flip the function to a conjunction, otherwise let it unchanged
			if (castedTermsFunctionName.equals("or")) {
				if (change) {
					Term[] para = castedTerm.getParameters();
					Term[] newPara = this.getNNF(para, change);
					return m_Script.term("and", newPara);
				}
				else {
					Term[] para = castedTerm.getParameters();
					Term[] newPara = this.getNNF(para, change);
					return m_Script.term("or", newPara);
				}
				
			}
			// If the function is implies, for example we have the following
			// (=> A B C) it is equivalent to (or (not A) (not B) C),
			// but instead of negating the first n - 1 we negate the last and
			// switch the change bool, so it is less work to do
			if (castedTermsFunctionName.equals("=>")) {
				// copy array of parameters
				Term[] para = castedTerm.getParameters();
				Term[] tempPara = new Term[para.length];
				for (int i = 0; i < para.length-1; i++){
					tempPara[i] = para[i];
				}
				// copy last parameter and negate it
				tempPara[tempPara.length-1] = m_Script.term("not",
														para[para.length-1]);
				// if there was a negation
				if (change) {
					change = false;
					Term[] newPara = this.getNNF(tempPara, change);
					return m_Script.term("and", newPara);
				}
				// there was no negation
				else {
					change = true;
					Term[] newPara = this.getNNF(tempPara, change);
					return m_Script.term("or", newPara);
				}
			}
		}
		// In this case we take the term, as a literal, because non of the
		// condition before matched, again we negate it if the change bit
		// is true and let in unchanged otherwise
		if (change) {
			return m_Script.term("not", term);
		}
		else {
			return term;
		}
	}
}
