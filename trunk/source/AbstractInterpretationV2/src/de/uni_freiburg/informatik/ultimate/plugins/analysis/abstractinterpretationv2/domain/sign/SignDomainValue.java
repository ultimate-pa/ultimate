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
public class SignDomainValue implements IEvaluationResult<SignDomainValue.Values> {

	private Values mValue;

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
	 * @return A new value after the intersection of the current value with the other value.
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
}