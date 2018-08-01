/*
 * TODO: Copyright.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;

/*
 * TODO: Comment.
 */
abstract class Quantifier {

	public abstract String getName();
}

/*
 * TODO: Comment.
 */
class Exists extends Quantifier {

	@Override
	public String getName() {
		return "exists";
	}
}

/*
 * TODO: Comment.
 */
class Forall extends Quantifier {

	@Override
	public String getName() {
		return "forall";
	}
}

/*
 * TODO: Comment.
 */
class SplittedTerm {

	public Object operator;
	public Term[] terms;
}

/*
 * TODO: Comment.
 */
public class MoNatDiffUtils {

	/*
	 * TODO: Comment.
	 */
	public static boolean isSetOfIntSort(Sort sort) {
		return sort.getName().equals("SetOfInt");
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isIntConstant(Term term) {
		return term instanceof ConstantTerm && SmtSortUtils.isIntSort(term.getSort());
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isFreeVariable(Term term) {
		return SmtUtils.isConstant(term) && (SmtSortUtils.isIntSort(term.getSort()) || isSetOfIntSort(term.getSort()));
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isQuantifiedVariable(Term term) {
		return term instanceof TermVariable
				&& (SmtSortUtils.isIntSort(term.getSort()) || isSetOfIntSort(term.getSort()));
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isVariable(Term term) {
		return isFreeVariable(term) || isQuantifiedVariable(term);
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isIntVariable(Term term) {
		return isVariable(term) && SmtSortUtils.isIntSort(term.getSort());
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isSetOfIntVariable(Term term) {
		return isVariable(term) && isSetOfIntSort(term.getSort());
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isNegatedIntVariable(Term term) {
		SplittedTerm splittedTerm = splitTerm(term);

		return equalsFunctionSymbol(splittedTerm.operator, "-") && splittedTerm.terms != null
				&& splittedTerm.terms.length == 1 && isIntVariable(splittedTerm.terms[0]);
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean isIntVariableMinusIntVariable(Term term) {
		SplittedTerm splittedTerm = splitTerm(term);

		return equalsFunctionSymbol(splittedTerm.operator, "-") && splittedTerm.terms != null
				&& splittedTerm.terms.length == 2 && isIntVariable(splittedTerm.terms[0])
				&& isIntVariable(splittedTerm.terms[1]);
	}
	
	/*
	 * TODO: Comment.
	 */
	public static boolean isIntVariablePlusIntConstant(Term term) {
		SplittedTerm splittedTerm = splitTerm(term);

		return equalsFunctionSymbol(splittedTerm.operator, "+") && splittedTerm.terms != null
				&& splittedTerm.terms.length == 2 && isIntVariable(splittedTerm.terms[0])
				&& isIntConstant(splittedTerm.terms[1]);
	}

	/*
	 * TODO: Comment.
	 */
	public static boolean equalsFunctionSymbol(Object object, String string) {
		return object instanceof FunctionSymbol && ((FunctionSymbol) object).getName().equals(string);
	}

	/*
	 * Converts a constant term of sort Int to Java-type int.
	 */
	public static int constantTermToInt(Term term) {
		if (!isIntConstant(term))
			throw new IllegalArgumentException("Term must be a ConstantTerm of sort Int.");

		Object value = ((ConstantTerm) term).getValue();

		if (value instanceof Rational)
			throw new AssertionError("Oooops, somebody forgot to implement this.");

		if (value instanceof BigInteger)
			return ((BigInteger) value).intValue();

		throw new AssertionError("Unknown type of integer value: " + value.getClass().getSimpleName());
	}

	/*
	 * TODO: Comment.
	 */
	public static SplittedTerm splitTerm(Term term) {
		SplittedTerm splittedTerm = new SplittedTerm();

		if (term instanceof QuantifiedFormula) {
			QuantifiedFormula quantifiedFormula = (QuantifiedFormula) term;
			int quantifier = quantifiedFormula.getQuantifier();
			splittedTerm.operator = quantifier == QuantifiedFormula.EXISTS ? new Exists() : new Forall();
			splittedTerm.terms = new Term[] { quantifiedFormula.getSubformula() };
		}

		if (term instanceof ApplicationTerm) {
			ApplicationTerm applicationTerm = (ApplicationTerm) term;
			splittedTerm.operator = applicationTerm.getFunction();
			splittedTerm.terms = applicationTerm.getParameters();
		}

		return splittedTerm;
	}
}