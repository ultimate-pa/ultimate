/*
 * Copyright (C) 2015-2016 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator.EvalResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainValue;

/**
 * Interval representation used inside the octagon abstract domain.
 * The intervals have nothing to do with octagons.
 * <p>
 * All interval bounds are inclusive.
 * Unbounded intervals can be represented using the special value {@link OctValue#INFINITY} ({@code \inf}).
 * There is no constant for {@code -\inf}, therefore a lower bound of {@code \inf} represents {@code -\inf}.
 * Empty intervals have have a lower bound that is strictly greater than the upper bound.
 * There is no unique representation for the empty interval.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class OctInterval {

	/**
	 * Lower bound (inclusive) of this interval.
	 * A lower bound of {@link OctValue#INFINITY} represents the lower bound {@code -\inf}.
	 */
	private final OctValue mMin;
	
	/**
	 * Upper bound (inclusive) of this interval. 
	 */
	private final OctValue mMax;

	/**
	 * Creates a new interval from the given {@link IntervalDomainValue}.
	 * 
	 * @param ivlInterval Interval to be represented.
	 */
	public OctInterval(final IntervalDomainValue ivlInterval) {
		if (ivlInterval.isBottom()) {
			mMin = OctValue.ONE;
			mMax = OctValue.ZERO;
		} else {
			mMin = new OctValue(ivlInterval.getLower());
			mMax = new OctValue(ivlInterval.getUpper());
		}
	}

	/**
	 * Creates a new interval from the given bounds.
	 * 
	 * @param min Lower bound (inclusive). {@link OctValue#INFINITY} represents {@code -\inf}.
	 * @param max Upper bound (inclusive).
	 */
	public OctInterval(final OctValue min, final OctValue max) {
		mMin = min;
		mMax = max;
	}

	/**
	 * Creates the interval of allowed values for one variable from an octagon matrix.
	 * 
	 * @param octMat Octagon matrix
	 * @param varIdx
	 *            Index of the variable in the octagon matrix.
	 *            Index i corresponds to columns/rows 2i and 2i+1.
	 * @return Interval constraint for the given variable from the octagon
	 */
	public static OctInterval fromMatrix(final OctMatrix octMat, final int varIdx) {
		final int idx2 = varIdx * 2;
		final int idx21 = idx2 + 1;
		return new OctInterval(octMat.get(idx2, idx21).half().negateIfNotInfinity(), octMat.get(idx21, idx2).half());
	}

	/**
	 * Creates the interval of allowed results an expression of the form (±var1) - (±var2)
	 * can assume in an octagon matrix. The actual interval of results can be smaller than
	 * the interval returned by this method. Compute the closure of the octagon to get a
	 * minimal interval.
	 * 
	 * @param octMat Octagon matrix
	 * @param varIdx
	 *            Index of the variable in the octagon matrix.
	 *            Index i corresponds to a positive variable i/2 when even and to a negative variable floor(i/2) when odd.
	 * @return Interval constraint for the expression
	 */
	public static OctInterval fromMatrix(final OctMatrix octMat, final int var1Idx, final int var2Idx) {
		return new OctInterval(octMat.get(var1Idx, var2Idx).negateIfNotInfinity(), octMat.get(var2Idx, var1Idx));
	}

	/** Creates a new, unbounded interval {@code [-\inf, \inf]}. */
	public OctInterval() {
		mMin = mMax = OctValue.INFINITY;
	}

	/**
	 * Convert this interval to an {@link IntervalDomainValue}.
	 * 
	 * @return Converted interval
	 */
	public IntervalDomainValue toIvlInterval() {
		if (isBottom()) {
			return new IntervalDomainValue(true);
		}
		return new IntervalDomainValue(mMin.toIvlValue(), mMax.toIvlValue());
	}

	/** @return Lower bound (inclusive) of this interval. {@link OctValue#INFINITY} represents {@code -\inf}. */
	public OctValue getMin() {
		return mMin;
	}

	/** @return Upper bound (inclusive) of this interval. */
	public OctValue getMax() {
		return mMax;
	}
	
	/** @return This interval contains no values. */
	public boolean isBottom() {
		if (mMin.isInfinity()) { // [-inf, inf] is represeted as [inf, inf]
			return false;
		}
		return mMin.compareTo(mMax) > 0;
	}
	
	/** @return This interval contains all values (that is, the interval has no bounds). */
	public boolean isTop() {
		return mMin.isInfinity() && mMax.isInfinity();
	}

	/**
	 * Evaluates an expression of the form <i>x R c</i> with
	 * <ul>
	 *   <li>variable x ∈ this interval
	 *   <li>relation R from {@link RelationSymbol} (for instance =, ≤; ...)
	 *   <li>constant c
	 * </ul>
	 * 
	 * @param rel relation
	 * @param rightHandSide constant on the right hand side of the relation symbol

	 * @return {@link EvalResult#TRUE} iff interval empty or ∀ x ∈ this interval : x R c,
	 *         {@link EvalResult#FALSE} iff interval not empty and ∀ x ∈ this interval : ¬(x R c),
	 *         {@link EvalResult#UNKNOWN} otherwise.
	 */
	public EvalResult evaluate(final RelationSymbol rel, final Rational c) {
		if (isBottom()) {
			return EvalResult.TRUE;
		}
		final Rational lower = mMin.isInfinity() ? Rational.NEGATIVE_INFINITY : mMin.toRational();
		final Rational upper = mMax.toRational();
		switch(rel) {
		case DISTINCT:
			return EvalResult.selectTF(lower.compareTo(c) > 0 || upper.compareTo(c) < 0,
					lower.compareTo(c) == 0 && upper.compareTo(c) == 0);
		case EQ:
			return EvalResult.selectTF(lower.compareTo(c) == 0 && upper.compareTo(c) == 0,
					lower.compareTo(c) > 0 || upper.compareTo(c) < 0);
		case GEQ:
			return EvalResult.selectTF(lower.compareTo(c) >= 0, upper.compareTo(c) < 0);
		case GREATER:
			return EvalResult.selectTF(lower.compareTo(c) > 0, upper.compareTo(c) <= 0);
		case LEQ:
			return EvalResult.selectTF(upper.compareTo(c) <= 0, lower.compareTo(c) > 0);
		case LESS:
			return EvalResult.selectTF(upper.compareTo(c) < 0, lower.compareTo(c) >= 0);
		default:
			return EvalResult.UNKNOWN;
		}
	}
	
	@Override
	public String toString() {
		final StringBuilder strBuilder = new StringBuilder();
		strBuilder.append('[');
		if (mMin.isInfinity()) {
			strBuilder.append('-');
		}
		strBuilder.append(mMin).append("; ").append(mMax).append(']');
		return strBuilder.toString();
	}
}
