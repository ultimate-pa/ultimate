package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermException;


/**
 * Convert a formula into disjunctive normal form
 * Negation will be completely eliminated and we a left with a formula of
 * the following form
 * <pre>OR ( AND ( inequalities ) )</pre>
 * 
 * @author Jan Leike
 */
public class DNF implements PreProcessor {
	
	private Script m_script;
	
	@Override
	public String getDescription() {
		return "Transform the given term into disjunctive normal form.";
	}
	
	@Override
	public Term process(Script script, Term term) throws TermException {
		m_script = script;
		return Util.or(script, toDNF(term).toArray(new Term[0]));
	}
	
	/**
	 * DNF converter function
	 */
	private Collection<Term> toDNF(Term term) throws TermException {
		Collection<Term> clauses = new HashSet<Term>();
		if (!(term instanceof ApplicationTerm)) {
			clauses.add(term);
		} else {
			ApplicationTerm appt = (ApplicationTerm) term;
			if (appt.getFunction().getName().equals("and")) {
				List<Iterator<Term>> it_list = new ArrayList<Iterator<Term>>();
				List<Collection<Term>> dnfs = new ArrayList<Collection<Term>>();
				List<Term> current = new ArrayList<Term>();
				// Convert every parameter to DNF
				for (Term param : appt.getParameters()) {
					Collection<Term> dnf = toDNF(param);
					if (dnf.isEmpty()) {
						return clauses;
					}
					dnfs.add(dnf);
					Iterator<Term> it = dnf.iterator();
					current.add(it.next());
					it_list.add(it);
				}
				while (true) {
					clauses.add(Util.and(m_script,
							current.toArray(new Term[0])));
					
					// Advance the iterators
					int i = 0;
					while (i < it_list.size() && !it_list.get(i).hasNext()) {
						// Reset the iterator
						Iterator<Term> it = dnfs.get(i).iterator();
						current.set(i, it.next());
						it_list.set(i, it);
						++i;
					}
					if (i >= it_list.size()) {
						break; // All permutations have been considered
					}
					Term t = it_list.get(i).next();
					current.set(i, t);
				}
			} else if (appt.getFunction().getName().equals("or")) {
				for (Term param : appt.getParameters()) {
					clauses.addAll(toDNF(param));
				}
			} else if (appt.getFunction().getName().equals("not")) {
				assert (appt.getParameters().length == 1);
				Term notTerm = appt.getParameters()[0];
				if ((notTerm instanceof TermVariable)) {
					clauses.add(notTerm);
				} else if (notTerm instanceof ApplicationTerm) {
					clauses.add(negateAtom((ApplicationTerm) notTerm));
				} else {
					throw new TermException("Expected an ApplicationTerm or "
							+ "TermVariable after negation", appt);
				}
			} else if (appt.getFunction().getName() == "=>") {
				clauses.addAll(toDNF(m_script.term("not",
						appt.getParameters()[0])));
				clauses.addAll(toDNF(appt.getParameters()[1]));
			} else if (appt.getFunction().getName() == "=" &&
					appt.getParameters()[0].getSort().getName().equals("Bool")) {
				Term param1 = appt.getParameters()[0];
				Term param2 = appt.getParameters()[1];
				clauses.addAll(toDNF(Util.and(m_script, 
						m_script.term("=>", param1, param2),
						m_script.term("=>", param2, param1))));
			} else {
				clauses.add(appt);
			}
		}
		return clauses;
	}
	
	/**
	 * Negate an atomary formula (an inequality term)
	 * @param script current SMT script
	 * @param term atomary term
	 * @return negated term
	 * @throws TermException if an error occurs while walking the term
	 */
	private Term negateAtom(ApplicationTerm term) throws TermException {
		Term[] params = term.getParameters();
		String fname = term.getFunction().getName();
		assert (params.length == 2) : "chaining not supported";
		if (fname.equals("<=")) {
			return m_script.term(">", params);
		} else if (fname.equals(">=")) {
			return m_script.term("<", params);
		} else if (fname.equals("<")) {
			return m_script.term(">=", params);
		} else if (fname.equals(">")) {
			return m_script.term("<=", params);
		} else {
			throw new TermException("Unexpected atom structure", term);
		}
	}
}