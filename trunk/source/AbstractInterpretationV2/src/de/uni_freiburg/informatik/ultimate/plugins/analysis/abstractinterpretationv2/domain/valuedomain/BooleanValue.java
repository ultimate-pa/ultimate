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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Represents a boolean value in abstract interpretation. The value can either be <code>true</code>, <code>false</code>,
 * &top;, or &bot;.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class BooleanValue {

	public enum Value {
		TRUE, FALSE, TOP, BOTTOM
	}

	private Value mValue;

	/**
	 * Default constructor. The constructed boolean value is &top;.
	 */
	public BooleanValue() {
		mValue = Value.TOP;
	}

	/**
	 * Sets the constructed boolean value to the given value.
	 * 
	 * @param value
	 *            The value to set.
	 */
	public BooleanValue(boolean value) {
		if (value) {
			mValue = Value.TRUE;
		} else {
			mValue = Value.FALSE;
		}
	}

	/**
	 * Sets the constructed boolean value to the given value in string representation.
	 * 
	 * @param value
	 *            The value to set.
	 */
	public BooleanValue(String value) {
		this(Boolean.parseBoolean(value));
	}

	/**
	 * Sets the constructed boolean value to the given value.
	 * 
	 * @param value
	 *            The value to set.
	 */
	public BooleanValue(Value value) {
		mValue = value;
	}

	/**
	 * Sets the constructed boolean value to the given value.
	 * 
	 * @param value
	 *            The value to set.
	 */
	public BooleanValue(BooleanValue value) {
		mValue = value.getValue();
	}

	/**
	 * @return The value of the {@link BooleanValue}.
	 */
	public Value getValue() {
		return mValue;
	}

	@Override
	public boolean equals(Object other) {
		if (other == null) {
			return false;
		}

		if (!(other instanceof BooleanValue) && !(other instanceof Boolean)) {
			return false;
		}

		if (other instanceof Boolean) {
			final Boolean otherBool = (Boolean) other;

			switch (mValue) {
			case FALSE:
				return !otherBool;
			case TRUE:
				return otherBool;
			case TOP:
			case BOTTOM:
				return false;
			default:
				throw new UnsupportedOperationException("The boolean value type " + mValue + " is not implemented.");
			}
		}

		final BooleanValue o = (BooleanValue) other;
		return mValue == o.mValue;
	}

	/**
	 * Intersects this with another {@link BooleanValue}.
	 * 
	 * @param other
	 *            The value to intersect with.
	 * @return A new boolean value corresponding to the result of the intersection.
	 */
	public BooleanValue intersect(BooleanValue other) {
		assert other != null;

		if (mValue == other.mValue) {
			return new BooleanValue(mValue);
		}

		if (mValue == Value.TOP) {
			return new BooleanValue(other.mValue);
		}

		if (other.mValue == Value.TOP) {
			return new BooleanValue(mValue);
		}

		return new BooleanValue(Value.BOTTOM);
	}

	/**
	 * Merges this with another {@link BooleanValue}.
	 * 
	 * @param other
	 *            The other boolean value to merge with.
	 * @return A new boolean value corresponding to the result of the merging.
	 */
	public BooleanValue merge(BooleanValue other) {
		assert other != null;

		if (mValue == Value.BOTTOM || other.mValue == Value.BOTTOM) {
			return new BooleanValue(Value.BOTTOM);
		}

		if (!equals(other)) {
			return new BooleanValue(Value.TOP);
		}

		return new BooleanValue(mValue);
	}

	/**
	 * The logical and operator (similar to &&).
	 * 
	 * @param other
	 *            The other value.
	 * @return A new {@link BooleanValue} corresponding to the result of the application of the logical and operator.
	 */
	public BooleanValue and(BooleanValue other) {
		assert other != null;

		if (mValue == Value.BOTTOM || other.mValue == Value.BOTTOM) {
			return new BooleanValue(Value.BOTTOM);
		}

		if (mValue == Value.FALSE || other.mValue == Value.FALSE) {
			return new BooleanValue(false);
		}

		if (mValue == Value.TRUE && other.mValue == Value.TRUE) {
			return new BooleanValue(true);
		}

		return new BooleanValue(Value.TOP);
	}

	/**
	 * The logical or operator (similar to ||).
	 * 
	 * @param other
	 *            The other value.
	 * @return A new {@link BooleanValue} corresponding to the result of the application of the logical or operator.
	 */
	public BooleanValue or(BooleanValue other) {
		assert other != null;

		if (mValue == Value.BOTTOM && other.mValue == Value.BOTTOM) {
			return new BooleanValue(Value.BOTTOM);
		}

		if (mValue == Value.TRUE || other.mValue == Value.TRUE) {
			return new BooleanValue(true);
		}

		if (mValue == Value.TOP || other.mValue == Value.TOP) {
			return new BooleanValue(Value.TOP);
		}

		return new BooleanValue(false);
	}

	/**
	 * The logical negation operator (similar to !).
	 * 
	 * @return A new {@link BooleanValue} corresponding to the result of the application of the logical negation
	 *         opeartor.
	 */
	public BooleanValue neg() {
		if (mValue == Value.TRUE) {
			return new BooleanValue(false);
		}

		if (mValue == Value.FALSE) {
			return new BooleanValue(true);
		}

		if (mValue == Value.TOP) {
			return new BooleanValue(Value.TOP);
		}

		return new BooleanValue(Value.BOTTOM);
	}

	@Override
	public String toString() {
		final StringBuilder stringBuilder = new StringBuilder();

		switch (mValue) {
		case TRUE:
			stringBuilder.append("TRUE");
			break;
		case FALSE:
			stringBuilder.append("FALSE");
			break;
		case TOP:
			stringBuilder.append("TOP");
			break;
		case BOTTOM:
			stringBuilder.append("BOTTOM");
			break;
		default:
			throw new UnsupportedOperationException("The boolean value type " + mValue + " is not implemented.");
		}

		return stringBuilder.toString();
	}

	public Term getTerm(final Script script, final Sort sort, final Term var) {
		switch (mValue) {
		case BOTTOM:
			return script.term("false");
		case TOP:
			return script.term("true");
		case FALSE:
			return script.term("=", var, script.term("false"));
		case TRUE:
			return script.term("=", var, script.term("true"));
		default:
			throw new UnsupportedOperationException("The boolean value type " + mValue + " is not implemented.");
		}
	}
}
