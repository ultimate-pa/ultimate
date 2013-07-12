package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import java.util.*;

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
	 * @returns the linear inequality
	 * @throws TermException if the input term cannot be reduced to a
	 *         LinearInequality
	 */
	private static LinearInequality convertAtom(Script script,
			ApplicationTerm term) throws TermException {
		if (term.getParameters().length != 2) {
			throw new TermIsNotAffineException(
					"Unsupported number of parameters", term);
		}
		String fname = term.getFunction().getName();
		LinearInequality li1 = LinearInequality.fromTerm(script,
				term.getParameters()[0]);
		LinearInequality li2 = LinearInequality.fromTerm(script,
				term.getParameters()[1]);
		LinearInequality res;
		if (fname == ">=") {
			li2.mult(Rational.MONE);
			res = li1;
			res.add(li2);
			res.strict = false;
		} else if (fname == "<=") {
			li1.mult(Rational.MONE);
			res = li1;
			res.add(li2);
			res.strict = false;
		} else if (fname == ">") {
			li2.mult(Rational.MONE);
			res = li1;
			res.add(li2);
			res.strict = true;
		} else if (fname == "<") {
			res = li1;
			res.mult(Rational.MONE);
			res.add(li2);
			res.strict = true;
		} else {
			throw new TermIsNotAffineException("Expected an inequality.", term);
		}
		return res;
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
				LinearInequality li = new LinearInequality();
				terms.add(li);
			} else if (fname == "=")  {
				Term param0 = appt.getParameters()[0];
				Sort param0sort = param0.getSort();
				if (param0sort.isNumericSort()) {
					terms.add(convertAtom(script, appt));
				} else if (param0sort.getName().equals("Bool")) {
					throw new TermException("Term is not in DNF", term);
				} else {
					throw new TermException("Unknown sort in equality", term);
				}
			} else if (fname == "<" || fname == ">"
					|| fname == "<=" || fname == ">=") {
				terms.add(convertAtom(script, appt));
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
