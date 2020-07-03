package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTermUtils.TriFunction;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public abstract class AbstractAssumption implements IAssumption{

	protected final Sort mSort;
	protected final Script mScript;
	protected final TriFunction<Script, Sort, Term, Term> mRhsAppender;

	protected abstract Term constructContractedLhs();
	protected abstract Term[] getConjunctsForExplicitForm();

	protected AbstractAssumption(final Script script, final Sort sort,
								 final TriFunction<Script, Sort, Term, Term> rhsConstructor) {
		mSort = sort;
		mScript = script;
		mRhsAppender = rhsConstructor;
	}

	@Override
	public Sort getSort() {
		return mSort;
	}

	@Override
	public Term toContractedTermIfPossible() {
		Term lhs;
		if (hasContractedForm()) {
			lhs = constructContractedLhs();
		}else {
			return toExplicitTerm();
		}
		return mRhsAppender.apply(mScript, mSort, lhs);
	}

	@Override
	public Term toExplicitTerm() {
		return SmtUtils.and(mScript, getConjunctsForExplicitForm());
	}

	@Override
	public String toString() {
		return toExplicitTerm().toString();
	}
}
