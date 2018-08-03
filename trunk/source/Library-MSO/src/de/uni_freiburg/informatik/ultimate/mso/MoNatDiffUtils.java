/*
 * TODO: Copyright.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
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
	 * TODO: Remove sort check here. Add isQuantifiedVariable, isFreeVariable of each sort.
	 */
	public static boolean isIntVariable(Term term) {
		return isVariable(term) && SmtSortUtils.isIntSort(term.getSort());
	}

	/*
	 * TODO: Comment.
	 * TODO: Remove sort check here. Add isQuantifiedVariable, isFreeVariable of each sort.
	 */
	public static boolean isSetOfIntVariable(Term term) {
		return isVariable(term) && isSetOfIntSort(term.getSort());
	}
}