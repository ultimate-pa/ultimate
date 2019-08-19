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
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.relationchecker;

import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain.IDomain;

/**
 * Checks relations between abstract states such as {@code  σ = ⊥} or {@code  σ1 ⊆ σ2}.
 * Such checks can be answered using a solver or methods from {@link IDomain}. The latter case
 * may require to abstract the states. Due to the nature of abstraction the result is only correct
 * for the abstracted states such that succeding computations have to be performed with the abstracted
 * states instead, therefore the (possibly altered) inputs are returned by each check.
 *
 * @deprecated  Replaced by relation checks in {@link IDomain}.
 *              Still kept for copy-pasting parts of this deprecated code when needed in the new code
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public interface IRelationChecker {

	/**
	 * Represents the relation check »<i>left-hand side, relation, right-hand side</i>«.
	 * We use this to return the actually checked relation, meaning due to abstraction the operands can differ
	 * from the queried relation check.
	 *
	 * @author schaetzc@tf.uni-freiburg.de
	 */
	public static class LhsRelRhs {
		protected IPredicate mLhs;
		protected IPredicate mRhs;
		protected boolean mResult;
		protected boolean mAbstracted;
		public LhsRelRhs(final IPredicate lhs, final IPredicate rhs) {
			this(lhs, rhs, false, false);
		}
		public LhsRelRhs(final IPredicate lhs, final IPredicate rhs, final boolean result, final boolean abstracted) {
			mLhs = lhs;
			mRhs = rhs;
			mResult = result;
			mAbstracted = abstracted;
		}
		public IPredicate getLhs() {
			return mLhs;
		}
		public IPredicate getRhs() {
			return mRhs;
		}
		public boolean isTrue() {
			return mResult;
		}
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

	LhsRelRhs isEqBottom(IPredicate pred);

	LhsRelRhs isSubsetEq(IPredicate left, IPredicate right);

	/**
	 * Quick isBottom check allowing for false negatives without having to alter the input.
	 * <p>
	 * The contract for this method can be formulated as any of the following points
	 * <ul>
	 * <li> pred ⇒ ¬underapproxIsBottom(pred)
	 * <li> underapproxIsBottom(pred) ⇒ ¬pred
	 * <li> (pred ≠ ⊥) ⇒ ¬underapproxIsBottom(pred)
	 * <li> underapproxIsBottom(pred) ⇒ (pred = ⊥)
	 * <li> For states distinct from bottom the result is always false.<br>
	 *      For states equal to bottom the result is true with some luck but can also be false
	 *      if equality to bottom is not obvious.
	 * </ul>
	 * Therefore {@code return false} is a valid implementation of this method.
	 *
	 * @param pred A predicate to be checked for equality to bottom
	 * @return pred is obviously unsatisfiable
	 */
	boolean underapproxIsBottom(IPredicate pred);

	/**
	 * Quick isSubsetEq check allowing for false negatives without having to alter the inputs.
	 * <p>
	 * The contract for this method can be formulated as any of the following points
	 * <ul>
	 * <li> ¬(left → right) ⇒ ¬underapproxIsSubsetEq(left, right)
	 * <li> underapproxIsSubsetEq(left, right) ⇒ (left → right)
	 * <li> left ⊋ right ⇒ ¬underapproxIsSubsetEq(left, right)
	 * <li> underapproxIsSubsetEq(left, right) ⇒ (left ⊆ right)
	 * </ul>
	 * Therefore {@code return false} is a valid implementation of this method.
	 *
	 * @param left left-hand side of the ⊆ relation
	 * @param right right-hand side of the ⊆ relation
	 * @return (left, right) is obviously in ⊆-relation.
	 */
	boolean underapproxIsSubsetEq(IPredicate left, IPredicate right);
}
