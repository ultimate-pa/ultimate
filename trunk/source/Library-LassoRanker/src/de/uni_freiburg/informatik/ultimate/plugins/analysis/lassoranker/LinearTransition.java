package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.*;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.InequalityConverter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.IntegralHull;


/**
 * A LinearTransition is a finite union of polyhedra
 * 
 * Essentially, this class is a wrapper for List<List<Inequality>> with a
 * pretty toString() method.
 * 
 * @author Jan Leike
 */
public class LinearTransition {
	
	private List<List<LinearInequality>> m_polyhedra;
	private boolean m_contains_integers;
	
	public LinearTransition(List<List<LinearInequality>> polyhedra) {
		assert(polyhedra != null);
		for (List<LinearInequality> polyhedron : polyhedra) {
			assert(polyhedron != null);
		}
		m_polyhedra = polyhedra;
		
		m_contains_integers = false;
		for (List<LinearInequality> polyhedron : polyhedra) {
			for (LinearInequality ieq : polyhedron) {
				for (TermVariable var : ieq.getVariables()) {
					if (var.getSort().getName().equals("Int")) {
						m_contains_integers = true;
						return;
					}
				}
			}
		}
	}
	
	/**
	 * Convert a term into a list of clauses
	 * @param term a term in disjunctive normal form
	 * @return list of clauses
	 */
	private static List<Term> toClauses(Term term) {
		List<Term> l = new ArrayList<Term>();
		if (!(term instanceof ApplicationTerm)) {
			l.add(term);
			return l;
		}
		ApplicationTerm appt = (ApplicationTerm) term;
		if (!appt.getFunction().getName().equals("or")) {
			l.add(term);
			return l;
		}
		for (Term t : appt.getParameters()) {
			l.addAll(toClauses(t));
		}
		return l;
	}
	
	/**
	 * Convert a term in the proper form into a linear transition.
	 * 
	 * The term must be in DNF, contain no negations, and only atoms in
	 * the form a <= b, a < b, a >= b, and a > b, with a and b being linear
	 * expressions.
	 * 
	 * @param term the input term
	 * @throws TermException if the supplied term does not have the correct form
	 */
	public static LinearTransition fromTerm(Term term) throws TermException {
		List<List<LinearInequality>> polyhedra =
				new ArrayList<List<LinearInequality>>();
		for (Term disjunct : toClauses(term)) {
			polyhedra.add(InequalityConverter.convert(disjunct));
		}
		return new LinearTransition(polyhedra);
	}
	
	/**
	 * @return whether this linear transition contains any integer variables
	 */
	public boolean containsIntegers() {
		return m_contains_integers;
	}
	
	/**
	 * Compute the integral hull of each polyhedron
	 */
	public void integralHull() {
		for (List<LinearInequality> polyhedron : m_polyhedra) {
			polyhedron.addAll(IntegralHull.compute(polyhedron));
		}
	}
	
	/**
	 * @return whether this transition contains only one polyhedron
	 */
	public boolean isConjunctive() {
		return m_polyhedra.size() <= 1;
	}
	
	/**
	 * @return the number of polyhedra (number of disjuncts)
	 */
	public int getNumPolyhedra() {
		return m_polyhedra.size();
	}
	
	/**
	 * @return the total number of inequalities in all polyhedra 
	 */
	public int getNumInequalities() {
		int num = 0;
		for (List<LinearInequality> polyhedron : m_polyhedra) {
			num += polyhedron.size();
		}
		return num;
	}
	
	/**
	 * @return all variables occuring in any of the inequalities
	 */
	public Set<TermVariable> getVariables() {
		Set<TermVariable> vars = new HashSet<TermVariable>();
		for (List<LinearInequality> polyhedron : m_polyhedra) {
			for (LinearInequality li : polyhedron) {
				vars.addAll(li.getVariables());
			}
		}
		return vars;
	}
	
	/**
	 * @return this transition's polyhedra as a list
	 */
	public List<List<LinearInequality>> getPolyhedra() {
		return Collections.unmodifiableList(m_polyhedra);
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("(OR\n");
		for (List<LinearInequality> polyhedron : m_polyhedra) {
			sb.append("    (AND\n");
			for (LinearInequality ieq : polyhedron) {
				sb.append("        ");
				sb.append(ieq);
				sb.append("\n");
			}
			sb.append("    )\n");
		}
		sb.append(")");
		return sb.toString();
	}
}
