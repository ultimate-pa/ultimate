package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

final class ReplaceByFreshTerm extends Substitution {
	
	public ReplaceByFreshTerm(Term match) {
		super(match);
	}

	private Cmd m_Add;
	
	private final static String FRESH_PREFIX="@DELTA_DEBUG_FRESH_";
	private static int freshnum = 0;
	private final static Sort[] EMPTY_SORT_ARRAY = {};
	
	private static String getNextFreshName() {
		return FRESH_PREFIX + (++freshnum);
	}
	
	@Override
	public Term apply(Term input) {
		String funname = getNextFreshName();
		m_Add = new DeclareFun(funname, EMPTY_SORT_ARRAY, input.getSort());
		Theory t = input.getTheory();
		return t.term(
				t.declareFunction(
						funname, EMPTY_SORT_ARRAY, input.getSort()));
	}

	@Override
	public Cmd getAdditionalCmd(Term input) {
		return m_Add;
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		PrintTerm pt = new PrintTerm();
		pt.append(sb, getMatch());
		sb.append(" ==> fresh");
		return sb.toString();
	}
	
}