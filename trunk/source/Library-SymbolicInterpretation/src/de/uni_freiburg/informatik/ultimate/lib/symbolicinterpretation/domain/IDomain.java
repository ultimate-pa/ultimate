/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Abstract Domain for Symbolic Interpretation with Fluid Abstractions (Sifa).
 * 
 * @author schaetzc@tf.uni-freiburg.de
 *
 * @param <ABS_STATE> Type of the abstract states of this domain. Should be fixed for subclasses.
 */
public interface IDomain {

	// special symbols for copy-pasting: ∀ ¬ ⇒ ⇏ ≢ ≡ α ∪ ∨

	/**
	 * Joins two abstract states.
	 * <p>
	 * The join of two abstract states is similar their union, that is, logical disjunction (∨). However, the exact
	 * union might not be expressible as an abstract state, therefore the join may over-approximate the union
	 * similar to α(p1 ∨ p2).
	 * 
	 * @param first p1
	 * @param second p2
	 * @return Join j of p1 and p2 such that (p1 ∨ p2) → j.
	 */
	IPredicate join(IPredicate first, IPredicate second);

	/**
	 * Widens one abstract state by another one.
	 * <p>
	 * Widening is similar to {@link #join(IPredicate, IPredicate)} with the additional property  that on any infinite
	 * sequence p1, p2, p3, ... the sequence w1, w2, w3, ... with w1 = p1 and wi = widen(w(i-1), pi) reaches a fixpoint,
	 * that is, wi = w(i+1) = w(i+2) = ... for some i.
	 * 
	 * @param old Old abstract state to be widened by widenWith
	 * @param widenWith New abstract state extending old
	 * @return Widened abstract state
	 */
	IPredicate widen(IPredicate old, IPredicate widenWith);

	/**
	 * Checks unsatisfiability.
	 * The check has to be precise and has always to terminate. This is only possible since the
	 * input is an abstract state and not an arbitrary predicate.
	 *
	 * @param pred Predicate to be checked
	 * @return The predicate is unsatisfiable, that is, equivalent to false
	 */
	boolean isBottom(IPredicate pred);

	/**
	 * Checks whether the set of concrete states described by predicate p1 is a subset of or equal to the set of
	 * concrete states described by predicate p2, that is p1 → p2.
	 * <p>
	 * The check has to be precise and has always to terminate. This is only possible since the
	 * input is an abstract state and not an arbitrary predicate.
	 * 
	 * @param subset p1
	 * @param superset p2
	 * @return p1 → p2
	 */
	boolean isSubsetEq(final IPredicate subset, final IPredicate superset);

	/**
	 * Abstracts a predicate by over-approximating, that is ∀ p : p → α(p).
	 * Ideally, the abstraction is idempotent, that is ∀ p : α(p) ≡ α(α(p)).
	 * @param pred Predicate to be abstracted
	 * @return Abstracted predicate
	 */
	IPredicate alpha(IPredicate pred);
}
