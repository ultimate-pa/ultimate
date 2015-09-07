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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluationResult;

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
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class SignDomainValue implements IEvaluationResult<SignDomainValue.Values>, Comparable<SignDomainValue> {

	private static final int BUILDER_SIZE = 100;

	private final Values mValue;

	/**
	 * The possible values of one {@link SignDomainValue}.
	 * 
	 * @author greitsch@informatik.uni-freiburg.de
	 *
	 */
	public enum Values {
		POSITIVE, NEGATIVE, ZERO, BOTTOM, TOP,
	}

	/**
	 * Default constructor. The default value of the {@link SignDomainValue} is T.
	 */
	protected SignDomainValue() {
		mValue = Values.TOP;
	}

	/**
	 * Constructor that sets the value of the created {@link SignDomainValue}.
	 * 
	 * @param value
	 *            The value the SignDomainValue should be set to. Must be one of {@link Values}.
	 */
	protected SignDomainValue(Values value) {
		mValue = value;
	}

	/**
	 * Returns the value of the current {@link SignDomainValue}.
	 */
	@Override
	public Values getResult() {
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
	protected SignDomainValue intersect(SignDomainValue other) {

		if (mValue == other.getResult() && mValue == Values.POSITIVE) {
			return new SignDomainValue(Values.POSITIVE);
		}
		if (mValue == other.getResult() && mValue == Values.ZERO) {
			return new SignDomainValue(Values.ZERO);
		}
		if (mValue == other.getResult() && mValue == Values.TOP) {
			return new SignDomainValue(Values.TOP);
		}

		// In all other cases, return \bot
		return new SignDomainValue(Values.BOTTOM);
	}

	@Override
	public int hashCode() {
		return getResult().hashCode();
	}

	@Override
	public boolean equals(Object other) {
		if (other == null) {
			return false;
		}

		if (other == this) {
			return true;
		}

		if (this.getClass() == other.getClass()) {
			final SignDomainValue castedOther = (SignDomainValue) other;
			return getResult() == castedOther.getResult();
		}
		return false;
	}

	@Override
	/**
	 * Implements the following relations and their inverse according to the lattice of the sign domain:
	 * 
	 * <p>
	 * &bot; == &bot;
	 * (-) == (-)
	 * (+) == (+)
	 * T == T
	 * &bot; < ..., where ... is not &bot;
	 * (-) < 0
	 * (-) < (+)
	 * (0) < (+)
	 * ... < T, where ... is not T
	 * </p>
	 * 
	 * <p>
	 *        T
	 *    /   |   \
	 * (-) - (0) - (+)
	 *    \   |   /
	 *      &bot;
	 * </p>
	 */
	public int compareTo(SignDomainValue other) {

		// ... == ...
		if (getResult() == other.getResult()) {
			return 0;
		}
		// ... == ...

		// \bot < ...
		if (getResult() == Values.BOTTOM && other.getResult() != Values.BOTTOM) {
			return -1;
		}
		if (getResult() != Values.BOTTOM && other.getResult() == Values.BOTTOM) {
			return 1;
		}
		// \bot < ...

		// (-) < ...
		if (getResult() == Values.NEGATIVE && other.getResult() != Values.NEGATIVE) {
			return -1;
		}
		if (getResult() != Values.NEGATIVE && other.getResult() == Values.NEGATIVE) {
			return 1;
		}
		// (-) < ...

		// (0) < ...
		if (getResult() == Values.ZERO && other.getResult() != Values.ZERO) {
			return -1;
		}
		if (getResult() != Values.ZERO && other.getResult() == Values.ZERO) {
			return 1;
		}
		// (0) < ...

		// \top > ...
		if (getResult() != Values.TOP && other.getResult() == Values.TOP) {
			return -1;
		}
		if (getResult() == Values.TOP && other.getResult() != Values.TOP) {
			return 1;
		}
		// \top > ...

		final StringBuilder stringBuilder = new StringBuilder(BUILDER_SIZE);
		stringBuilder.append("The case for this = ").append(getResult()).append(" and other = ")
		        .append(other.getResult()).append(" is not implemented.");
		throw new UnsupportedOperationException(stringBuilder.toString());
	}
}
