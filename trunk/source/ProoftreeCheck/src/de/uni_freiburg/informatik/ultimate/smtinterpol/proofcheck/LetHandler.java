package de.uni_freiburg.informatik.ultimate.smtinterpol.proofcheck;

import java.util.HashMap;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.*;

/**
 * This class is used to abbreviate a lemma in the proof.
 * 
 * As abbreviation a prefix followed by the number assigned by SMTInterpol
 * is written in the Isabelle proof.
 * The string is partly taken from the SMTInterpol term variable name
 * '.cseX', where X is a unique number.
 * 
 * @author Christian Schilling
 */
public class LetHandler {
	// mapping from let variable to represented lemma
	private final HashMap<TermVariable, Term> m_let2Term;
	
	/**
	 * constructor
	 */
	public LetHandler() {
		m_let2Term = new HashMap<TermVariable, Term>();
	}
	
	/**
	 * This method reads the unique part from the term variable name.
	 * It is a number, but is only used as a string.
	 * 
	 * @param variable the term variable
	 * @return the number associated with this variable
	 */
	public String getNumberString(TermVariable variable) {
		String name = variable.getName();
		assert ((name.startsWith(".cse")) && (name.length() > 4));
		return name.substring(4);
	}
	
	/**
	 * This method returns the lemma given the SMTInterpol abbreviation.
	 * 
	 * @param variable abbreviation used by SMTInterpol
	 * @return the lemma (term and number)
	 */
	public Term getLemma(TermVariable variable) {
		assert (m_let2Term.get(variable) != null);
		return m_let2Term.get(variable);
	}
	
	/**
	 * This method adds a new lemma.
	 * 
	 * @param variable term variable used by SMTInterpol.
	 * @param term abbreviated term
	 */
	public void add(TermVariable variable, Term term) {
		assert (! m_let2Term.containsKey(variable));
		m_let2Term.put(variable, term);
	}
	
	/**
	 * This method clears the map between two subsequent proofs.
	 */
	public void clear() {
		m_let2Term.clear();
	}
	
	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();
		
		builder.append("{");
		String append = "";
		for (Entry<TermVariable, Term> entry : m_let2Term.entrySet()) {
			builder.append(append);
			append = ", ";
			builder.append(entry.getKey().toString());

			builder.append(" ~> ");
			builder.append(entry.getValue().toStringDirect());
		}
		builder.append("}");
		
		return builder.toString();
	}
}