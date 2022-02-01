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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.ITermProvider;

/**
 * Represents a boolean value in abstract interpretation. The value can either be <code>true</code>, <code>false</code>,
 * &top;, or &bot;.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public enum BooleanValue implements ITermProvider {

	/**
	 * Exactly true.
	 */
	TRUE,
	/**
	 * Exactly false.
	 */
	FALSE,
	/**
	 * Either true or false.
	 */
	TOP,
	/**
	 * Neither true nor false
	 */
	BOTTOM,
	/**
	 * Type error or some other error.
	 */
	INVALID;

	/**
	 * Sets the constructed boolean value to the given value.
	 *
	 * @param value
	 *            The value to set.
	 */
	public static BooleanValue getBooleanValue(final boolean value) {
		return value ? TRUE : FALSE;
	}

	/**
	 * Sets the constructed boolean value to the given value in string representation.
	 *
	 * @param value
	 *            The value to set.
	 */
	public static BooleanValue getBooleanValue(final String value) {
		return getBooleanValue(Boolean.parseBoolean(value));
	}

	/**
	 * Returns <code>true</code> if and only if the other object is equal to <code>this</code>.
	 *
	 * @param other
	 *            The other object to compare.
	 * @return <code>true</code> if and only if the value of the other Boolean is equal to the value of
	 *         <code>this</code>.
	 */
	public boolean isEqualTo(final BooleanValue other) {
		if (other == null) {
			return false;
		}

		return this == other;
	}

	/**
	 * Returns <code>true</code> if this is contained in other.
	 *
	 * @param other
	 *            The other state to check against.
	 * @return <code>true</code> if and only if the value of this is contained in the value of other, <code>false</code>
	 *         otherwise.
	 */
	public boolean isContainedIn(final BooleanValue other) {
		if (other == null) {
			return false;
		}
		if (other == TOP) {
			return true;
		}
		if (other == this) {
			return true;
		}
		return this == BOTTOM;
	}

	/**
	 * @return <code>true</code> if and only if the value of <code>this</code> is &bot;, <code>false</code> otherwise.
	 */
	public boolean isBottom() {
		return this == BOTTOM;
	}

	/**
	 * Intersects this with another {@link BooleanValue}.
	 *
	 * @param other
	 *            The value to intersect with.
	 * @return A new boolean value corresponding to the result of the intersection.
	 */
	public BooleanValue intersect(final BooleanValue other) {
		assert other != null;

		if (this == other) {
			return this;
		}

		if (this == TOP) {
			return other;
		}

		if (other == TOP) {
			return this;
		}

		return BOTTOM;
	}

	/**
	 * Merges this with another {@link BooleanValue}.
	 *
	 * @param other
	 *            The other boolean value to merge with.
	 * @return A new boolean value corresponding to the result of the merging.
	 */
	public BooleanValue merge(final BooleanValue other) {
		assert other != null;

		if (this == BOTTOM && other == BOTTOM) {
			return this;
		}

		if (this == BOTTOM && other != BOTTOM) {
			return other;
		} else if (this != BOTTOM && other == BOTTOM) {
			return this;
		}

		if (!isEqualTo(other)) {
			return TOP;
		}
		return this;
	}

	/**
	 * The logical and operator (similar to &&).
	 *
	 * @param other
	 *            The other value.
	 * @return A new {@link BooleanValue} corresponding to the result of the application of the logical and operator.
	 */
	public BooleanValue and(final BooleanValue other) {
		assert other != null;

		if (this == BOTTOM || other == BOTTOM) {
			return BOTTOM;
		}

		if (this == FALSE || other == FALSE) {
			return FALSE;
		}

		if (this == TRUE && other == TRUE) {
			return TRUE;
		}

		return TOP;
	}

	/**
	 * The logical or operator (similar to ||).
	 *
	 * @param other
	 *            The other value.
	 * @return A new {@link BooleanValue} corresponding to the result of the application of the logical or operator.
	 */
	public BooleanValue or(final BooleanValue other) {
		assert other != null;

		if (this == BOTTOM || other == BOTTOM) {
			return BOTTOM;
		}

		if (this == TRUE || other == TRUE) {
			return TRUE;
		}

		if (this == TOP || other == TOP) {
			return TOP;
		}

		return FALSE;
	}

	/**
	 * The logical negation operator (similar to !).
	 *
	 * @return A new {@link BooleanValue} corresponding to the result of the application of the logical negation
	 *         opeartor.
	 */
	public BooleanValue neg() {
		if (this == TRUE) {
			return FALSE;
		}

		if (this == FALSE) {
			return TRUE;
		}

		if (this == TOP) {
			return TOP;
		}

		return BOTTOM;
	}

	@Override
	public Term getTerm(final Script script, final Sort sort, final Term var) {
		assert sort.equals(var.getSort());
		switch (this) {
		case BOTTOM:
			return script.term("false");
		case TOP:
			return script.term("true");
		case FALSE:
			return SmtUtils.not(script, var);
		case TRUE:
			return var;
		default:
			throw new UnsupportedOperationException("The boolean value type " + this + " is not implemented.");
		}
	}

	/**
	 * @return true if this {@link BooleanValue} is either {@link BooleanValue#TRUE} or {@link BooleanValue#FALSE}
	 *         (i.e., represents only a single value), false otherwise.
	 */
	public boolean isSingleton() {
		return this == FALSE || this == TRUE;
	}
}
