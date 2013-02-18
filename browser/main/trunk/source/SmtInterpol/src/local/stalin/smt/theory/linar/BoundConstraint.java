package local.stalin.smt.theory.linar;

import java.util.Collections;
import java.util.Set;

import local.stalin.logic.Formula;
import local.stalin.logic.Term;
import local.stalin.logic.Theory;
import local.stalin.smt.dpll.Clause;
import local.stalin.smt.dpll.DPLLAtom;
import local.stalin.smt.dpll.Literal;

/**
 * Class representing an upper bound (var <= bound) on a variable.
 * 
 * @author Juergen Christ
 */
public class BoundConstraint extends DPLLAtom {

	InfinitNumber mbound;
	// Lazy generated inverse bound.
	InfinitNumber ibound;
	LinVar mvar;

	// Save the old bound to be able to backtrack this constraint
	InfinitNumber oldbound;
	// Save the old literal to be able to backtrack this constraint
	Literal oldassert;

	// Save explanation for bound refinement propagation since it cannot be
	// recreated
	Literal[] mpropexpl;
	Rational[] mpropexplcoeffs;
	Clause cutexpl;

	public BoundConstraint(InfinitNumber bound, LinVar var) {
		mbound = bound;
		if (var.misint) {
			assert(bound.ma.isIntegral() && bound.mb == Rational.ZERO);
			ibound = bound.add(new InfinitNumber(Rational.ONE, Rational.ZERO));
		} else {
			ibound = new InfinitNumber(mbound.ma, mbound.mb
				.equals(Rational.ZERO) ? Rational.ONE : Rational.ZERO);
		}
		mvar = var;
		assert !mvar.mconstraints.containsKey(bound);
		mvar.mconstraints.put(bound, this);
		oldbound = null;
		oldassert = null;
		mpropexpl = null;
		mpropexplcoeffs = null;
	}

	public LinVar getVar() {
		return mvar;
	}

	/**
	 * Return the bound if this atom should be true (var <= bound).
	 * 
	 * @return Bound set during construction
	 */
	public InfinitNumber getBound() {
		return mbound;
	}

	/**
	 * Return the bound if this atom should be false (ibound <= var).
	 * 
	 * @return Bound converted to lower bound.
	 */
	public InfinitNumber getInverseBound() {
		return ibound;
	}

	@Override
	public String toStringNegated() {
		InfinitNumber ibound = getInverseBound();
		if (ibound.mb.equals(Rational.ONE))
			return "["+hashCode()+"]"+mvar + " > " + ibound.ma;
		else
			return "["+hashCode()+"]"+mvar + " >= " + ibound;
	}

	public String toString() {
		if (mbound.mb.equals(Rational.MONE))
			return "["+hashCode()+"]"+mvar + " < " + mbound.ma;
		else
			return "["+hashCode()+"]"+mvar + " <= " + mbound;
	}

	// / --- Implies checks ---
	/**
	 * Is this constraint implied by a given upper bound?
	 * 
	 * This function returns <code>true</code> iff this bound is bigger than
	 * the given bound.
	 * 
	 * @param ubound
	 *            Upper bound currently set.
	 * @return true iff this bound is bigger than <code>ubound</code>.
	 */
	boolean impliedByUpperBound(InfinitNumber ubound) {
		return ubound.lesseq(mbound);
	}

	/**
	 * Is this constraint implied by a given lower bound?
	 * 
	 * This function returns <code>true</code> iff this bound is smaller than
	 * the given bound.
	 * 
	 * @param lbound
	 *            Lower bound currently set.
	 * @return true iff this bound is smaller than <code>lbound</code>.
	 */
	boolean impliedByLowerBound(InfinitNumber lbound) {
		return getInverseBound().lesseq(lbound);
	}

	@Override
	public Formula getSMTFormula(Theory smtTheory) {
		MutableAffinTerm at = new MutableAffinTerm(mvar.misint);
		at.add(Rational.ONE, mvar);
		at.add(mbound.negate());
		Set<BoundConstraint> empty = Collections.emptySet();
		return new LinInterpolant(at, empty).createFormula(smtTheory);
	}

	@Override
	public Formula getNegatedSMTFormula(Theory smtTheory) {
		MutableAffinTerm at = new MutableAffinTerm(mvar.misint);
		at.add(Rational.MONE, mvar);
		at.add(ibound);
		Set<BoundConstraint> empty = Collections.emptySet();
		return new LinInterpolant(at, empty).createFormula(smtTheory);
	}

	/**
	 * Create an interpolation term for this constraint.
	 * 
	 * @param positive
	 *            Is this atom asserted as positive literal?
	 * @param ih
	 *            Helper to convert variables and terms into SMTLIB.
	 * @return Interpolation term representing this constraint.
	 */
	public void combineInterpolationTerm(MutableAffinTerm at, Rational coeff,
			boolean positive) {
		if (positive) {
			// We have var <= bound ==> var - bound <= 0
			at.add(coeff, mvar);
			at.add(mbound.mul(coeff).negate());
		} else {
			// We have ibound <= var ==> -var + ibound <= 0
			at.add(coeff.negate(), mvar);
			at.add(ibound.mul(coeff));
		}
	}

	/**
	 * Create an interpolation term for this constraint.
	 * 
	 * @param positive
	 *            Is this atom asserted as positive literal?
	 * @param ih
	 *            Helper to convert variables and terms into SMTLIB.
	 * @return Interpolation term representing this constraint.
	 */
	public void combineMixedInterpolationTerm(MutableAffinTerm at,
			Rational coeff, boolean positive, int cutpos) {
		if (positive) {
			// We have a-local <= ?x ==> alocal - ?x <= 0
			at.add(coeff.negate(), mvar.mixedVar);
			at.addALocal(coeff, mvar, cutpos);
		} else {
			// We have a-local >= ?x ==> ?x - alocal <= 0 
			at.add(coeff, mvar.mixedVar);
			at.addALocal(coeff.negate(), mvar, cutpos);
		}
	}

	@Override
	public int getFirstFormulaNr() {
		return mvar.getFirstFormulaNr();
	}

	@Override
	public int getLastFormulaNr() {
		return mvar.getLastFormulaNr();
	}

	@Override
	public int containsTerm(Term t) {
		if (mvar.isInitiallyBasic()) {
			LinTerm lt = (LinTerm) mvar.mname;
			for (LinVar v : lt.mcoeffs.keySet()) {
				if (((Term) v.mname).containsSubTerm(t))
					return 1;
			}
			return 0;
		}
		return ((Term) mvar.mname).containsSubTerm(t) ? 1 : 0;
	}
}
