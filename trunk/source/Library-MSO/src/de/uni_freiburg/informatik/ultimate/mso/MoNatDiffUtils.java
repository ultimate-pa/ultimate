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
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;

/*
 *  TODO: Comment.
 */
class SplittedTerm {
	public String operator = new String();
	public List<Term> terms = new ArrayList<Term>();
}

/*
 * TODO: Comment.
 * Questions: How to deal with constant values larger than max int?
 */
public class MoNatDiffUtils {

	/*
	 * Converts a constant term of sort Int to Java-type int.
	 */
	public static int constantTermToInt(Term term) {
		
		if (!SmtSortUtils.isIntSort(term.getSort()))
			throw new IllegalArgumentException("Term must be of sort Int.");
		
		if (!(term instanceof ConstantTerm))
			throw new IllegalArgumentException("Term must be of type ConstantTerm.");
		
		final Object value = ((ConstantTerm)term).getValue();
		
		if (value instanceof Rational)
			throw new AssertionError("Oooops, somebody forgot to implement this.");
		
		if (value instanceof BigInteger)
			return ((BigInteger)value).intValue();
				
		throw new AssertionError("Unknown type of integer value: " + value.getClass().getSimpleName());
	}
	
	/*
	 * TODO: Comment.
	 */
	public static boolean isSetOfIntSort(Term term) {
		
		return term.getSort().getName().equals("SetOfInt");
	}
	
	/*
	 * TODO: Comment.
	 */
	public static boolean isFreeVariable(Term term) {
		
		return SmtUtils.isConstant(term) && (SmtSortUtils.isIntSort(term.getSort()) || isSetOfIntSort(term));
	}
	
	/*
	 * TODO: Comment.
	 */
	public static boolean isQuantifiedVariable(Term term) {
		
		return term instanceof TermVariable && (SmtSortUtils.isIntSort(term.getSort()) || isSetOfIntSort(term));
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
	public static SplittedTerm splitTerm(Term term) {
		SplittedTerm splittedTerm = new SplittedTerm();
	
		if (term instanceof QuantifiedFormula) {
			QuantifiedFormula quantifiedFormula = (QuantifiedFormula)term;
			splittedTerm.operator = quantifiedFormula.getQuantifier() == QuantifiedFormula.EXISTS ? "exists": "forall";
			splittedTerm.terms.add(quantifiedFormula.getSubformula());
		}
		
		if (term instanceof ApplicationTerm) {
			ApplicationTerm applicationTerm = (ApplicationTerm)term;
			splittedTerm.operator = applicationTerm.getFunction().getName();
			splittedTerm.terms.addAll(Arrays.asList(applicationTerm.getParameters()));
		}
		
		return splittedTerm;
	}
	
}