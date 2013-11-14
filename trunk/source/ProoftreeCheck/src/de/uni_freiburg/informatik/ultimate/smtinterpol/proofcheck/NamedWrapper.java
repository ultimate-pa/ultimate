package de.uni_freiburg.informatik.ultimate.smtinterpol.proofcheck;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * This class wraps a function definition from a :named annotation to be
 * written later on.
 */
public class NamedWrapper {
	final String m_name;
	final Term m_subterm;
	
	/**
	 * @param name the name
	 * @param subterm the sub-term
	 */
	public NamedWrapper(final String name, final Term subterm) {
		m_name = name;
		m_subterm = subterm;
	}
	
	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("[");
		builder.append(m_name);
		builder.append(", ");
		builder.append(m_subterm.toStringDirect());
		builder.append("]");
		return builder.toString();
	}
}