/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.explicit;

import java.util.Collection;
import java.util.Collections;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;

/**
 * Representation of an explicit value in the {@link ExplicitValueDomain}
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ExplicitValueValue extends BaseExplicitValueValue {

	private final Rational mValue;

	public ExplicitValueValue(final Rational value) {
		assert value != null;
		mValue = value;
	}

	@Override
	public BaseExplicitValueValue copy() {
		return this;
	}

	@Override
	public boolean isBottom() {
		return false;
	}

	@Override
	public boolean isTop() {
		return false;
	}

	@Override
	public BaseExplicitValueValue intersect(final BaseExplicitValueValue other) {
		return commutativeOp(other, other::intersect, evv -> {
			if (evv.mValue.equals(mValue)) {
				return this;
			}
			return ExplicitValueBottom.DEFAULT;
		});
	}

	@Override
	public BaseExplicitValueValue merge(final BaseExplicitValueValue other) {
		return commutativeOp(other, other::merge, evv -> {
			if (evv.mValue.equals(mValue)) {
				return this;
			}
			return ExplicitValueTop.DEFAULT;
		});
	}

	@Override
	public Collection<BaseExplicitValueValue> complement() {
		return Collections.singleton(ExplicitValueTop.DEFAULT);
	}

	@Override
	public Collection<BaseExplicitValueValue> complementInteger() {
		return Collections.singleton(ExplicitValueTop.DEFAULT);
	}

	@Override
	public boolean isAbstractionEqual(final BaseExplicitValueValue other) {
		return commutativeOp(other, other::isAbstractionEqual, evv -> evv.mValue.equals(mValue));
	}

	@Override
	public boolean isContainedIn(final BaseExplicitValueValue other) {
		if (other.isTop()) {
			return true;
		}
		if (other.isBottom()) {
			return false;
		}
		return isAbstractionEqual(other);
	}

	@Override
	public BaseExplicitValueValue add(final BaseExplicitValueValue other) {
		return commutativeOp(other, other::add, evv -> new ExplicitValueValue(mValue.add(evv.mValue)));
	}

	@Override
	public BaseExplicitValueValue subtract(final BaseExplicitValueValue other) {
		return nonCommutativeOpCanonical(other, evv -> new ExplicitValueValue(mValue.sub(evv.mValue)));
	}

	@Override
	public BaseExplicitValueValue multiply(final BaseExplicitValueValue other) {
		return commutativeOp(other, other::multiply, evv -> new ExplicitValueValue(mValue.mul(evv.mValue)));
	}

	@Override
	public BaseExplicitValueValue negate() {
		return new ExplicitValueValue(mValue.negate());
	}

	@Override
	public BaseExplicitValueValue divideInteger(final BaseExplicitValueValue other) {
		// TODO: Ensure that is euclidedan
		return nonCommutativeOpCanonical(other,
				evv -> new ExplicitValueValue(AbsIntUtil.euclideanDivision(mValue, evv.mValue)));
	}

	@Override
	public BaseExplicitValueValue divideReal(final BaseExplicitValueValue other) {
		return nonCommutativeOpCanonical(other, evv -> new ExplicitValueValue(mValue.div(evv.mValue)));
	}

	@Override
	public BaseExplicitValueValue modulo(final BaseExplicitValueValue other) {
		if (other.isTop()) {
			return other;
		}
		if (other.isBottom()) {
			return other;
		}
		final ExplicitValueValue evv = (ExplicitValueValue) other;
		return new ExplicitValueValue(AbsIntUtil.euclideanModulo(mValue, evv.mValue));
	}

	@Override
	public BaseExplicitValueValue greaterThan(final BaseExplicitValueValue other) {
		return nonCommutativeOpCanonical(other, this::greaterThan);
	}

	public BaseExplicitValueValue greaterThan(final ExplicitValueValue other) {
		return nonCommutativeOpCanonical(other,
				evv -> mValue.compareTo(evv.mValue) == 1 ? this : ExplicitValueBottom.DEFAULT);
	}

	@Override
	public BooleanValue isEqual(final BaseExplicitValueValue other) {
		return nonCommutativeOpCanonicalBoolean(other,
				evv -> mValue.equals(evv.mValue) ? BooleanValue.TRUE : BooleanValue.FALSE);
	}

	@Override
	public BooleanValue isNotEqual(final BaseExplicitValueValue other) {
		return nonCommutativeOpCanonicalBoolean(other,
				evv -> mValue.equals(evv.mValue) ? BooleanValue.FALSE : BooleanValue.TRUE);
	}

	@Override
	public BooleanValue isGreaterThan(final BaseExplicitValueValue other) {
		return nonCommutativeOpCanonicalBoolean(other,
				evv -> mValue.compareTo(evv.mValue) > 0 ? BooleanValue.TRUE : BooleanValue.FALSE);
	}

	@Override
	public BaseExplicitValueValue greaterOrEqual(final BaseExplicitValueValue other) {
		return nonCommutativeOpCanonical(other,
				evv -> mValue.compareTo(evv.mValue) >= 0 ? this : ExplicitValueBottom.DEFAULT);
	}

	@Override
	public BooleanValue isGreaterOrEqual(final BaseExplicitValueValue other) {
		return nonCommutativeOpCanonicalBoolean(other,
				evv -> mValue.compareTo(evv.mValue) >= 0 ? BooleanValue.TRUE : BooleanValue.FALSE);
	}

	@Override
	public BaseExplicitValueValue lessThan(final BaseExplicitValueValue other) {
		return nonCommutativeOpCanonical(other,
				evv -> mValue.compareTo(evv.mValue) == -1 ? this : ExplicitValueBottom.DEFAULT);
	}

	@Override
	public BooleanValue isLessThan(final BaseExplicitValueValue other) {
		return nonCommutativeOpCanonicalBoolean(other,
				evv -> mValue.compareTo(evv.mValue) < 0 ? BooleanValue.TRUE : BooleanValue.FALSE);
	}

	@Override
	public BaseExplicitValueValue lessOrEqual(final BaseExplicitValueValue other) {
		return nonCommutativeOpCanonical(other,
				evv -> mValue.compareTo(evv.mValue) <= 0 ? this : ExplicitValueBottom.DEFAULT);
	}

	@Override
	public BooleanValue isLessOrEqual(final BaseExplicitValueValue other) {
		return nonCommutativeOpCanonicalBoolean(other,
				evv -> mValue.compareTo(evv.mValue) <= 0 ? BooleanValue.TRUE : BooleanValue.FALSE);
	}

	@Override
	public BaseExplicitValueValue inverseModulo(final BaseExplicitValueValue referenceValue,
			final BaseExplicitValueValue oldValue, final boolean isLeft) {
		return oldValue;
	}

	@Override
	public BaseExplicitValueValue inverseEquality(final BaseExplicitValueValue oldValue,
			final BaseExplicitValueValue referenceValue) {
		return referenceValue;
	}

	@Override
	public BaseExplicitValueValue inverseLessOrEqual(final BaseExplicitValueValue oldValue, final boolean isLeft) {
		return oldValue;
	}

	@Override
	public BaseExplicitValueValue inverseLessThan(final BaseExplicitValueValue oldValue, final boolean isLeft) {
		return oldValue;
	}

	@Override
	public BaseExplicitValueValue inverseGreaterOrEqual(final BaseExplicitValueValue oldValue, final boolean isLeft) {
		return oldValue;
	}

	@Override
	public BaseExplicitValueValue inverseGreaterThan(final BaseExplicitValueValue oldValue, final boolean isLeft) {
		return oldValue;
	}

	@Override
	public BaseExplicitValueValue inverseNotEqual(final BaseExplicitValueValue oldValue,
			final BaseExplicitValueValue referenceValue) {
		return oldValue;
	}

	@Override
	public Term getTerm(final Script script, final Sort sort, final Term variable) {
		return script.term("=", variable, SmtUtils.rational2Term(script, mValue, sort));
	}

	private <T> T commutativeOp(final BaseExplicitValueValue other, final Function<BaseExplicitValueValue, T> distFun,
			final Function<ExplicitValueValue, T> fun) {
		if (other instanceof ExplicitValueValue) {
			final ExplicitValueValue evv = (ExplicitValueValue) other;
			return fun.apply(evv);
		}
		return distFun.apply(this);
	}

	private static <T> T nonCommutativeOp(final BaseExplicitValueValue other,
			final Function<BaseExplicitValueValue, T> botFun, final Function<BaseExplicitValueValue, T> topFun,
			final Function<ExplicitValueValue, T> fun) {
		if (other.isTop()) {
			return topFun.apply(other);
		}
		if (other.isBottom()) {
			return botFun.apply(other);
		}
		final ExplicitValueValue evv = (ExplicitValueValue) other;
		return fun.apply(evv);
	}

	private static BaseExplicitValueValue nonCommutativeOpCanonical(final BaseExplicitValueValue other,
			final Function<ExplicitValueValue, BaseExplicitValueValue> fun) {
		if (other.isTop()) {
			return ExplicitValueTop.DEFAULT;
		}
		if (other.isBottom()) {
			return ExplicitValueBottom.DEFAULT;
		}
		final ExplicitValueValue evv = (ExplicitValueValue) other;
		return fun.apply(evv);
	}

	private static BooleanValue nonCommutativeOpCanonicalBoolean(final BaseExplicitValueValue other,
			final Function<ExplicitValueValue, BooleanValue> fun) {
		if (other.isTop()) {
			return BooleanValue.TOP;
		}
		if (other.isBottom()) {
			return BooleanValue.BOTTOM;
		}
		final ExplicitValueValue evv = (ExplicitValueValue) other;
		return fun.apply(evv);
	}

	@Override
	public String toString() {
		return mValue.toString();
	}

}
