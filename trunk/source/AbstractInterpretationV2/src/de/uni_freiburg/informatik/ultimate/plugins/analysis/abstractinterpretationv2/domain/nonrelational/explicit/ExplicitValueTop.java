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

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;

/**
 * Representation of an explicit value in the {@link ExplicitValueDomain}
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ExplicitValueTop extends BaseExplicitValueValue {

	public static final ExplicitValueTop DEFAULT = new ExplicitValueTop();

	private ExplicitValueTop() {
		// singleton private constructor
	}

	@Override
	public boolean isBottom() {
		return false;
	}

	@Override
	public boolean isTop() {
		return true;
	}

	@Override
	public BaseExplicitValueValue intersect(final BaseExplicitValueValue other) {
		return other;
	}

	@Override
	public BaseExplicitValueValue merge(final BaseExplicitValueValue other) {
		return this;
	}

	@Override
	public Collection<BaseExplicitValueValue> complement() {
		return Collections.singleton(ExplicitValueBottom.DEFAULT);
	}

	@Override
	public Collection<BaseExplicitValueValue> complementInteger() {
		return complement();
	}

	@Override
	public boolean isAbstractionEqual(final BaseExplicitValueValue other) {
		return other == this;
	}

	@Override
	public boolean isContainedIn(final BaseExplicitValueValue other) {
		return other == this;
	}

	@Override
	public BaseExplicitValueValue add(final BaseExplicitValueValue other) {
		return bottomOrThis(other);
	}

	@Override
	public BaseExplicitValueValue subtract(final BaseExplicitValueValue other) {
		return bottomOrThis(other);
	}

	@Override
	public BaseExplicitValueValue multiply(final BaseExplicitValueValue other) {
		return bottomOrThis(other);
	}

	@Override
	public BaseExplicitValueValue negate() {
		return this;
	}

	@Override
	public BaseExplicitValueValue divideInteger(final BaseExplicitValueValue other) {
		return bottomOrThis(other);
	}

	@Override
	public BaseExplicitValueValue divideReal(final BaseExplicitValueValue other) {
		return bottomOrThis(other);
	}

	@Override
	public BaseExplicitValueValue modulo(final BaseExplicitValueValue other) {
		return bottomOrThis(other);
	}

	@Override
	public BaseExplicitValueValue greaterThan(final BaseExplicitValueValue other) {
		return bottomOrThis(other);
	}

	@Override
	public BooleanValue isEqual(final BaseExplicitValueValue other) {
		return bottomOrThisBoolean(other);
	}

	@Override
	public BooleanValue isNotEqual(final BaseExplicitValueValue other) {
		return bottomOrThisBoolean(other);
	}

	@Override
	public BooleanValue isGreaterThan(final BaseExplicitValueValue other) {
		return bottomOrThisBoolean(other);
	}

	@Override
	public BaseExplicitValueValue greaterOrEqual(final BaseExplicitValueValue other) {
		return bottomOrThis(other);
	}

	@Override
	public BooleanValue isGreaterOrEqual(final BaseExplicitValueValue other) {
		return bottomOrThisBoolean(other);
	}

	@Override
	public BaseExplicitValueValue lessThan(final BaseExplicitValueValue other) {
		return bottomOrThis(other);
	}

	@Override
	public BooleanValue isLessThan(final BaseExplicitValueValue other) {
		return bottomOrThisBoolean(other);
	}

	@Override
	public BaseExplicitValueValue lessOrEqual(final BaseExplicitValueValue other) {
		return bottomOrThis(other);
	}

	@Override
	public BooleanValue isLessOrEqual(final BaseExplicitValueValue other) {
		return bottomOrThisBoolean(other);
	}

	@Override
	public BaseExplicitValueValue inverseModulo(final BaseExplicitValueValue referenceValue,
			final BaseExplicitValueValue oldValue, final boolean isLeft) {
		return bottomOrThis(referenceValue, oldValue);
	}

	@Override
	public BaseExplicitValueValue inverseEquality(final BaseExplicitValueValue oldValue,
			final BaseExplicitValueValue referenceValue) {
		return bottomOrThis(referenceValue, oldValue);
	}

	@Override
	public BaseExplicitValueValue inverseLessOrEqual(final BaseExplicitValueValue oldValue, final boolean isLeft) {
		return bottomOrThis(oldValue);
	}

	@Override
	public BaseExplicitValueValue inverseLessThan(final BaseExplicitValueValue oldValue, final boolean isLeft) {
		return bottomOrThis(oldValue);
	}

	@Override
	public BaseExplicitValueValue inverseGreaterOrEqual(final BaseExplicitValueValue oldValue, final boolean isLeft) {
		return bottomOrThis(oldValue);
	}

	@Override
	public BaseExplicitValueValue inverseGreaterThan(final BaseExplicitValueValue oldValue, final boolean isLeft) {
		return bottomOrThis(oldValue);
	}

	@Override
	public BaseExplicitValueValue inverseNotEqual(final BaseExplicitValueValue oldValue,
			final BaseExplicitValueValue referenceValue) {
		return bottomOrThis(referenceValue, oldValue);
	}

	@Override
	public Term getTerm(final Script script, final Sort sort, final Term referenceTerm) {
		return script.term("true");
	}

	private static BooleanValue bottomOrThisBoolean(final BaseExplicitValueValue other) {
		if (other.isBottom()) {
			return BooleanValue.BOTTOM;
		}
		return BooleanValue.TOP;
	}

	private BaseExplicitValueValue bottomOrThis(final BaseExplicitValueValue referenceValue,
			final BaseExplicitValueValue oldValue) {
		if (oldValue.isBottom() || referenceValue.isBottom()) {
			return oldValue;
		}
		return this;
	}

	private BaseExplicitValueValue bottomOrThis(final BaseExplicitValueValue other) {
		if (other.isBottom()) {
			return other;
		}
		return this;
	}

	@Override
	public String toString() {
		return "TOP";
	}

}
