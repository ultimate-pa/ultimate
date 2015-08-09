package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluationResult;

/**
 * A value in the signed domain. Such a value can be one of the following:<br />
 * <ul>
 * <li>(+)</li>
 * <li>(-)</li>
 * <li>(0)</li>
 * <li>T</li>
 * <li>&perp;</li>
 * </ul>
 * 
 * The default value is always T.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class SignDomainValue implements IEvaluationResult<SignDomainValue.Values>, Comparable<SignDomainValue> {

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
	 * Default constructor. The default value of the {@link SignDomainValue} is
	 * T.
	 */
	protected SignDomainValue() {
		mValue = Values.TOP;
	}

	/**
	 * Constructor that sets the value of the created {@link SignDomainValue}.
	 * 
	 * @param value
	 *            The value the SignDomainValue should be set to. Must be one of
	 *            {@link Values}.
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
	 * Intersects {@link this} with a given other value according to the
	 * following scheme:
	 * 
	 * <ul>
	 * <li>(+) &cap; (+) = (+)</li>
	 * <li>(-) &cap; (+) = &perp;</li>
	 * <li>(0) &cap; (0) = (0)</li>
	 * <li>(0) &cap; (+) = &perp;</li>
	 * <li>(0) &cap; (-) = &perp;</li>
	 * <li>T &cap; T = T</li>
	 * <li>T &cap; ... = &perp; (if ... != T)</li>
	 * <li>&perp; &cap; ... = &perp;</li>
	 * </ul>
	 * 
	 * @param other
	 *            The other value to intersect the current value with.
	 * @return A new value after the intersection of the current value with the
	 *         other value.
	 */
	public SignDomainValue intersect(SignDomainValue other) {

		if (mValue.equals(other.getResult()) && mValue.equals(Values.POSITIVE)) {
			return new SignDomainValue(Values.POSITIVE);
		}
		if (mValue.equals(other.getResult()) && mValue.equals(Values.ZERO)) {
			return new SignDomainValue(Values.ZERO);
		}
		if (mValue.equals(other.getResult()) && mValue.equals(Values.TOP)) {
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

		if (other.getClass().equals(this.getClass())) {
			SignDomainValue castedOther = (SignDomainValue) other;
			return getResult().equals(castedOther.getResult());
		}
		return false;
	}

	@Override
	/**
	 * Implements the following relations and their inverse according to the lattice of the sign domain:
	 * 
	 * \bot == \bot
	 * (-) == (-)
	 * (+) == (+)
	 * \top == \top
	 * \bot < ..., where ... is not \bot
	 * (-) < 0
	 * (-) < (+)
	 * (0) < (+)
	 * ... < \top, where ... is not \top
	 * 
	 *       top
	 *    /   |   \
	 * (-) - (0) - (+)
	 *    \   |   /
	 *       bot
	 */
	public int compareTo(SignDomainValue other) {

		// ... == ...
		if (getResult().equals(other.getResult())) {
			return 0;
		}
		// ... == ...

		// \bot < ...
		if (getResult().equals(Values.BOTTOM) && !other.getResult().equals(Values.BOTTOM)) {
			return -1;
		}
		if (!getResult().equals(Values.BOTTOM) && other.getResult().equals(Values.BOTTOM)) {
			return 1;
		}
		// \bot < ...

		// (-) < ...
		if (getResult().equals(Values.NEGATIVE) && !other.getResult().equals(Values.NEGATIVE)) {
			return -1;
		}
		if (!getResult().equals(Values.NEGATIVE) && other.getResult().equals(Values.NEGATIVE)) {
			return 1;
		}
		// (-) < ...

		// (0) < ...
		if (getResult().equals(Values.ZERO) && !other.getResult().equals(Values.ZERO)) {
			return -1;
		}
		if (!getResult().equals(Values.ZERO) && other.getResult().equals(Values.ZERO)) {
			return 1;
		}
		// (0) < ...

		// \top > ...
		if (!getResult().equals(Values.TOP) && other.getResult().equals(Values.TOP)) {
			return -1;
		}
		if (getResult().equals(Values.TOP) && !other.getResult().equals(Values.TOP)) {
			return 1;
		}
		// \top > ...

		throw new UnsupportedOperationException("The case for this = " + getResult().toString() + " and other = "
		        + other.getResult().toString() + " is not implemented.");
	}
}
