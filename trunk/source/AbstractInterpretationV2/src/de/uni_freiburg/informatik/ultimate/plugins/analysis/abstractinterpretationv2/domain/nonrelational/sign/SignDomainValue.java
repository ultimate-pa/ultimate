/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;

/**
 * A value in the signed domain. Such a value can be one of the following:<br />
 * <ul>
 * <li>(+)</li>
 * <li>(-)</li>
 * <li>(0)</li>
 * <li>T</li>
 * <li>&bot;</li>
 * </ul>
 *
 * <p>
 * The default value is always T.
 * </p>
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class SignDomainValue implements IEvaluationResult<SignDomainValue.SignValues>,
		INonrelationalValue<SignDomainValue>, Comparable<SignDomainValue> {

	private static final int BUILDER_SIZE = 100;

	private final SignValues mValue;

	/**
	 * The possible values of one {@link SignDomainValue}.
	 *
	 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
	 *
	 */
	public enum SignValues {
		POSITIVE, NEGATIVE, ZERO, BOTTOM, TOP,
	}

	/**
	 * Default constructor. The default value of the {@link SignDomainValue} is T.
	 */
	protected SignDomainValue() {
		mValue = SignValues.TOP;
	}

	/**
	 * Constructor that sets the value of the created {@link SignDomainValue}.
	 *
	 * @param value
	 *            The value the SignDomainValue should be set to. Must be one of {@link SignValues}.
	 */
	protected SignDomainValue(final SignValues value) {
		mValue = value;
	}

	/**
	 * Returns the value of the current {@link SignDomainValue}.
	 */
	@Override
	public SignValues getValue() {
		return mValue;
	}

	/**
	 * Intersects {@link this} with a given other value according to the following scheme:
	 *
	 * <ul>
	 * <li>(+) &cap; (+) = (+)</li>
	 * <li>(-) &cap; (+) = &bot;</li>
	 * <li>(0) &cap; (0) = (0)</li>
	 * <li>(0) &cap; (+) = &bot;</li>
	 * <li>(0) &cap; (-) = &bot;</li>
	 * <li>T &cap; T = T</li>
	 * <li>T &cap; ... = &bot; (if ... != T)</li>
	 * <li>&bot; &cap; ... = &bot;</li>
	 * </ul>
	 *
	 * @param other
	 *            The other value to intersect the current value with.
	 * @return A new value after the intersection of the current value with the other value.
	 */
	@Override
	public SignDomainValue intersect(final SignDomainValue other) {

		if (mValue == other.getValue() && mValue == SignValues.POSITIVE) {
			return new SignDomainValue(SignValues.POSITIVE);
		}
		if (mValue == other.getValue() && mValue == SignValues.ZERO) {
			return new SignDomainValue(SignValues.ZERO);
		}
		if (mValue == other.getValue() && mValue == SignValues.TOP) {
			return new SignDomainValue(SignValues.TOP);
		}

		// In all other cases, return \bot
		return new SignDomainValue(SignValues.BOTTOM);
	}

	@Override
	public int hashCode() {
		return getValue().hashCode();
	}

	@Override
	public boolean equals(final Object other) {
		if (other == null) {
			return false;
		}

		if (other == this) {
			return true;
		}

		if (this.getClass() == other.getClass()) {
			final SignDomainValue castedOther = (SignDomainValue) other;
			return getValue() == castedOther.getValue();
		}
		return false;
	}

	@Override
	/**
	 * Implements the following relations and their inverse according to the lattice of the sign domain:
	 *
	 * <p>
	 * &bot; == &bot; (-) == (-) (+) == (+) T == T &bot; < ..., where ... is not &bot; (-) < 0 (-) < (+) (0) < (+) ... <
	 * T, where ... is not T
	 * </p>
	 *
	 * <p>
	 * T / | \ (-) - (0) - (+) \ | / &bot;
	 * </p>
	 */
	public int compareTo(final SignDomainValue other) {

		// ... == ...
		if (getValue() == other.getValue()) {
			return 0;
		}
		// ... == ...

		// \bot < ...
		if (getValue() == SignValues.BOTTOM && other.getValue() != SignValues.BOTTOM) {
			return -1;
		}
		if (getValue() != SignValues.BOTTOM && other.getValue() == SignValues.BOTTOM) {
			return 1;
		}
		// \bot < ...

		// (-) < ...
		if (getValue() == SignValues.NEGATIVE && other.getValue() != SignValues.NEGATIVE) {
			return -1;
		}
		if (getValue() != SignValues.NEGATIVE && other.getValue() == SignValues.NEGATIVE) {
			return 1;
		}
		// (-) < ...

		// (0) < ...
		if (getValue() == SignValues.ZERO && other.getValue() != SignValues.ZERO) {
			return -1;
		}
		if (getValue() != SignValues.ZERO && other.getValue() == SignValues.ZERO) {
			return 1;
		}
		// (0) < ...

		// \top > ...
		if (getValue() != SignValues.TOP && other.getValue() == SignValues.TOP) {
			return -1;
		}
		if (getValue() == SignValues.TOP && other.getValue() != SignValues.TOP) {
			return 1;
		}
		// \top > ...

		final StringBuilder stringBuilder = new StringBuilder(BUILDER_SIZE);
		stringBuilder.append("The case for this = ").append(getValue()).append(" and other = ").append(other.getValue())
				.append(" is not implemented.");
		throw new UnsupportedOperationException(stringBuilder.toString());
	}

	@Override
	public BooleanValue getBooleanValue() {
		throw new UnsupportedOperationException("not implemented");
	}

	@Override
	public SignDomainValue copy() {
		return new SignDomainValue(mValue);
	}

	@Override
	public boolean isBottom() {
		return mValue == SignValues.BOTTOM;
	}

	@Override
	public boolean isTop() {
		return mValue == SignValues.TOP;
	}

	@Override
	public SignDomainValue merge(final SignDomainValue other) {
		throw new UnsupportedOperationException("not implemented");
	}

	@Override
	public boolean isEqualTo(final SignDomainValue other) {
		throw new UnsupportedOperationException("not implemented");
	}

	@Override
	public Term getTerm(final Script script, final Sort sort, final Term var) {
		throw new UnsupportedOperationException("not implemented");
	}

	@Override
	public boolean isContainedIn(final SignDomainValue otherValue) {
		throw new UnsupportedOperationException("not implemented");
	}

	@Override
	public SignDomainValue add(final SignDomainValue other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SignDomainValue subtract(final SignDomainValue other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SignDomainValue multiply(final SignDomainValue other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SignDomainValue divideInteger(final SignDomainValue other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SignDomainValue divideReal(final SignDomainValue other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SignDomainValue modulo(final SignDomainValue other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SignDomainValue greaterThan(final SignDomainValue other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BooleanValue isGreaterThan(final SignDomainValue other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SignDomainValue greaterOrEqual(final SignDomainValue other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BooleanValue isGreaterOrEqual(final SignDomainValue other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SignDomainValue lessThan(final SignDomainValue other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BooleanValue isLessThan(final SignDomainValue other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SignDomainValue lessOrEqual(final SignDomainValue other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BooleanValue isLessOrEqual(final SignDomainValue other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SignDomainValue inverseModulo(final SignDomainValue referenceValue, final SignDomainValue oldValue,
			final boolean isLeft) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SignDomainValue inverseEquality(final SignDomainValue oldValue, final SignDomainValue referenceValue) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SignDomainValue inverseLessOrEqual(final SignDomainValue oldValue, final boolean isLeft) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SignDomainValue inverseLessThan(final SignDomainValue oldValue, final boolean isLeft) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SignDomainValue inverseGreaterOrEqual(final SignDomainValue oldValue, final boolean isLeft) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SignDomainValue inverseGreaterThan(final SignDomainValue oldValue, final boolean isLeft) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SignDomainValue inverseNotEqual(final SignDomainValue oldValue, final SignDomainValue referenceValue) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean canHandleReals() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean canHandleModulo() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public BooleanValue compareEquality(final SignDomainValue secondOther) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BooleanValue compareInequality(final SignDomainValue secondOther) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SignDomainValue negate() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<SignDomainValue> complement() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<SignDomainValue> complementInteger() {
		// TODO Auto-generated method stub
		return null;
	}
}
