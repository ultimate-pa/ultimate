package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermIsNotAffineException;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.UnknownFunctionException;


/**
 * Generate a list of LinearInequality instances from a formula in disjunctive
 * normal form
 * 
 * @author Jan Leike
 */
public class InequalityConverter {
	
	/**
	 * Convert an atomary term that is an (in-)equality into an instance of
	 * LinearInequality
	 * @param term atomary term
	 * @param list LinearInequality list that holds the return values
	 * @throws TermException if the input term cannot be reduced to a
	 *         LinearInequality
	 */
	private static void convertAtom(Script script, ApplicationTerm term,
			Collection<LinearInequality> list) throws TermException {
		ApplicationTerm appt = (ApplicationTerm) term;
		if (appt.getParameters().length != 2) {
			throw new TermIsNotAffineException(
					"Unsupported number of parameters", appt);
		}
		String fname = appt.getFunction().getName();
		LinearInequality li1 = LinearInequality.fromTerm(script, appt.getParameters()[0]);
		LinearInequality li2 = LinearInequality.fromTerm(script, appt.getParameters()[1]);
		LinearInequality res;
		if (fname == "<=") {
			at2.mult(Rational.MONE);
			res = at1;
			res.add(at2);
		} else if (fname == ">=") {
			at1.mult(Rational.MONE);
			res = at1;
			res.add(at2);
		} else if (fname == "=") {
			at2.mult(Rational.MONE);
			at1.add(at2);
			res = new AffineTerm();
			res.add(at1);
			res.mult(Rational.MONE);
			list.add(res);
			res = at1;
		} else if (fname == "<") {
			at2.mult(Rational.MONE);
			res = at1;
			res.add(at2);
//			if (this.m_variable_domain == VariableDomain.INTEGERS) {
				res.add(Rational.ONE);
//			}
		} else if (fname == ">") {
			res = at1;
			res.mult(Rational.MONE);
			res.add(at2);
//			if (this.m_variable_domain == VariableDomain.INTEGERS) {
				res.add(Rational.ONE);
//			}
		} else {
			throw new TermIsNotAffineException("Expected an (in-)equality.",
					appt);
		}
		list.add(res);
	}
	
	/**
	 * Convert
	 * @param script
	 * @param term
	 * @return
	 * @throws TermException
	 */
	public static List<LinearInequality> convert(Script script, Term term)
			throws TermException {
		List<LinearInequality> terms = new ArrayList<LinearInequality>();
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appt = (ApplicationTerm) term;
			String fname = appt.getFunction().getName();
			if (fname == "and") {
				for (Term t : appt.getParameters()) {
					terms.addAll(convert(script, t));
				}
			} else if (fname == "true") {
				// Add trivial linear inequality 0 ≤ 0.
				LinearInequality li = new LinearInequality(script);
				terms.add(li);
			} else if (fname == "=")  {
				Term param0 = appt.getParameters()[0];
				Sort param0sort = param0.getSort();
				if (param0sort.isNumericSort()) {
					convertAtom(script, appt, terms);
				} else if (param0sort.getName().equals("Bool")) {
					throw new TermException("Term is not in DNF", term);
				} else {
					throw new TermException("Unknown sort in equality", term);
				}
			} else if (fname == "<" || fname == ">"
					|| fname == "<=" || fname == ">=") {
				convertAtom(script, appt, terms);
			} else {
				throw new UnknownFunctionException(appt);
			}
		} else if (term instanceof TermVariable)
			throw new TermException("Term is not in DNF", term);
		else {
			throw new TermException("Expected application term.", term);
		}
		return terms;
	}
}
