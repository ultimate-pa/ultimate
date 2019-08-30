/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Abstract Domain for Symbolic Interpretation with Fluid Abstractions (Sifa).
 * Unlike abstract domains from abstract interpretation this type of domain does not have a dedicated state
 * representation forcing us to abstract after every step. Operators of this domain type work with any state,
 * even with un-abstracted states that are not of the domain specific form.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public interface IDomain {

	// special symbols for copy-pasting: ∀ ¬ ⇒ ⇏ ≢ ≡ α ∪ ∨ ⊆ ⊇

	/**
	 * Represents the result of an relation check as {@link IDomain#isEqBottom(IPredicate)} or
	 * {@link IDomain#isSubsetEq(IPredicate, IPredicate)}}.  Since relation checks may over-approximate their inputs,
	 * results are not only a boolean (here {@link #isTrueForAbstraction()}}) but also include the actually used
	 * (that is, possibly over-approximated) inputs.
	 *
	 * @author schaetzc@tf.uni-freiburg.de
	 */
	public static class ResultForAlteredInputs {
		protected IPredicate mLhs;
		protected IPredicate mRhs;
		protected boolean mResult;
		protected boolean mAbstracted;
		public ResultForAlteredInputs(final IPredicate lhs, final IPredicate rhs) {
			this(lhs, rhs, false, false);
		}
		public ResultForAlteredInputs(final IPredicate lhs, final IPredicate rhs,
				final boolean result, final boolean abstracted) {
			mLhs = lhs;
			mRhs = rhs;
			mResult = result;
			mAbstracted = abstracted;
		}
		/**
		 * @return The left-hand side of the queried check or an over-approximation if {@link #wasAbstracted()}
		 */
		public IPredicate getLhs() {
			return mLhs;
		}
		/**
		 * @return The right-hand side of the queried check or an over-approximation if {@link #wasAbstracted()}
		 */
		public IPredicate getRhs() {
			return mRhs;
		}
		/**
		 * @return {@code someCheck(this.getLhs(), this.getRhs())} (mathematically speaking)
		 *         where {@code someCheck(originalLhs, originalRhs)} is the procedure returning this result object.
		 */
		public boolean isTrueForAbstraction() {
			return mResult;
		}
		/**
		 * @return The queried check could not be performed on the given inputs.
		 *         The check was done for over-approximations of the given inputs.
		 *         The altered inputs can be obtained from {@link #getLhs()} and {@link #getRhs()}.
		 */
		public boolean wasAbstracted() {
			return mAbstracted;
		}
		protected void abstractLhs(final Function<IPredicate, IPredicate> alpha) {
			mAbstracted = true;
			mLhs = alpha.apply(mLhs);
		}
		protected void abstractLhsAndRhs(final Function<IPredicate, IPredicate> alpha) {
			mAbstracted = true;
			mLhs = alpha.apply(mLhs);
			mRhs = alpha.apply(mRhs);
		}
	}

	/**
	 * Joins two abstract states.
	 * The join of two abstract states is an over-approximation of their union, that is, logical disjunction (∨).
	 * <p>
	 * Whether or not to over-approximate is up to the implementation at each call. This may return an arbitrary
	 * predicate. A domain-specific normal form is not required.
	 *
	 * @param lhs Left-hand side of the join p1
	 * @param rhs Right-hand side of the join p2
	 * @return Join j of p1 and p2 such that (p1 ∨ p2) → j.
	 */
	IPredicate join(IPredicate lhs, IPredicate rhs);

	/**
	 * Widens one abstract state by another one.
	 * <p>
	 * Widening is similar to {@link #join(IPredicate, IPredicate)} with the additional property  that on any infinite
	 * sequence p1, p2, p3, ... the sequence w1, w2, w3, ... with w1 = p1 and wi = widen(w(i-1), pi) reaches a fixpoint,
	 * that is, wi = w(i+1) = w(i+2) = ... for some i.
	 * <p>
	 * This may return an arbitrary predicate. A domain-specific normal form is not required.
	 *
	 * @param old Old abstract state to be widened by widenWith
	 * @param widenWith New abstract state extending old
	 * @return Widened abstract state
	 */
	IPredicate widen(IPredicate old, IPredicate widenWith);

	/**
	 * Checks unsatisfiability.
	 * Ideally, this checks whether the set of concrete states described by predicate p is empty.
	 * However, this may do the check for an over-approximation p# ⊇ p instead.
	 * <p>
	 * The actual check has to be precise and has to terminate. This is only possible since this operator
	 * is allowed to over-approximate the input.
	 *
	 * @param pred Predicate p to be checked, left-hand side (lhs) of the relation check
	 * @return p# is unsatisfiable, that is, equivalent to false<br>
	 *         where p# ⊇ p is some left-hand side (lhs) over-approximating p
	 */
	ResultForAlteredInputs isEqBottom(IPredicate pred);

	/**
	 * Checks subset relations.
	 * Ideally, this checks whether the set of concrete states described by predicate p1 is a subset of or equal to
	 * the set of concrete states described by predicate p2, that is p1 → p2.
	 * However, this may do the check for over-approximations p1# ⊇ p1 and p2# ⊇ p2 instead.
	 * <p>
	 * The actual check has to be precise and has to terminate. This is only possible since this operator
	 * is allowed to over-approximate both inputs.
	 *
	 * @param subset p1, left-hand side (lhs) of the relation check
	 * @param superset p2, right-hand side (rhs) of the relation check
	 * @return p1# → p2#, that is, p1# ⊆ p2#<br>
	 *         where p1# ⊇ p1 and p2# ⊇ p2 are the altered inputs over-approximating p1 and p2
	 */
	ResultForAlteredInputs isSubsetEq(final IPredicate subset, final IPredicate superset);

	/**
	 * Abstracts a predicate by over-approximating, that is ∀ p : p → α(p).
	 * Ideally, the abstraction is idempotent, that is ∀ p : α(p) ≡ α(α(p)).
	 * @param pred Predicate to be abstracted
	 * @return Abstracted predicate
	 */
	IPredicate alpha(IPredicate pred);
}
