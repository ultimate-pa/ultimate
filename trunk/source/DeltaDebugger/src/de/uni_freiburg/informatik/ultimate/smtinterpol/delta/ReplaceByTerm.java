package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

final class ReplaceByTerm extends Substitution {
	
	Term m_Replacement;
	
	public ReplaceByTerm(Term match, Term replacement) {
		super(match);
		m_Replacement = replacement;
	}

	@Override
	public Term apply(Term input) {
		return m_Replacement;
	}

	@Override
	public Cmd getAdditionalCmd(Term input) {
		return null;
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		PrintTerm pt = new PrintTerm();
		pt.append(sb, getMatch());
		sb.append(" ==> ");
		pt.append(sb, m_Replacement);
		return sb.toString();
	}
	
}