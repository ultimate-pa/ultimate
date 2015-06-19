package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomainState.SignDomainValue;

/**
 * The implementation of a simple merge operator on the sign domain. This operator can also be used as widening
 * operator.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 * @param <ACTION>
 * @param <VARDECL>
 */
public class SignMergeOperator<ACTION, VARDECL> implements IAbstractStateBinaryOperator<ACTION, VARDECL> {

	private SignStateConverter<ACTION, VARDECL> mStateConverter;

	protected SignMergeOperator(SignStateConverter<ACTION, VARDECL> stateConverter) {
		mStateConverter = stateConverter;
	}

	/**
	 * Merges two abstract states, first and second, into one new abstract state. All variables that occur in first must
	 * also occur in second.<br />
	 * 
	 * Assume, there is a variable with name "v". The value of "v" in first is v1 and the value of "v" in second is v2.<br />
	 * 
	 * It is distinguished between four cases for the resulting merged value of "v":<br />
	 * <ol>
	 * <li>v1 is equal to v2:<br />
	 * The resulting value will be v1.</li>
	 * <li>v1 is positive (negative) and v2 is negative (positive):<br />
	 * The resulting value will be \top.</li>
	 * <li>v1 is not 0 (is 0) and v2 is 0 (is not 0):<br />
	 * The resulting value will be \top.</li>
	 * <li>v1 is \bot or v2 is \bot:<br />
	 * The resulting value will be \bot.</li>
	 * </ol>
	 * 
	 * @param first
	 *            The first state to merge.
	 * @param second
	 *            The second state to merge.
	 */
	@Override
	public IAbstractState<ACTION, VARDECL> apply(IAbstractState<ACTION, VARDECL> first,
	        IAbstractState<ACTION, VARDECL> second) {
		assert first != null;
		assert second != null;

		final SignDomainState<ACTION, VARDECL> firstState = mStateConverter.getCheckedState(first);
		final SignDomainState<ACTION, VARDECL> secondState = mStateConverter.getCheckedState(second);

		if (!firstState.hasSameVariables(secondState)) {
			throw new UnsupportedOperationException("Cannot merge two states with a disjoint set of variables.");
		}

		SignDomainState<ACTION, VARDECL> newState = (SignDomainState<ACTION, VARDECL>) first.copy();

		final Map<String, VARDECL> variables = firstState.getVariables();
		final Map<String, SignDomainValue> firstValues = firstState.getValues();
		final Map<String, SignDomainValue> secondValues = secondState.getValues();

		for (Entry<String, VARDECL> entry : variables.entrySet()) {
			SignDomainValue value1 = firstValues.get(entry.getKey());
			SignDomainValue value2 = secondValues.get(entry.getKey());

			// If both values are equal, the resulting value will stay the same.
			if (value1.equals(value2)) {
				newState.setValue(entry.getKey(), value1);
				continue;
			}

			// If v1 is positive (negative) and v2 is negative (positive), the resulting value will be \top.
			if ((value1.equals(SignDomainValue.POSITIVE) && value2.equals(SignDomainValue.NEGATIVE))
			        || (value1.equals(SignDomainValue.NEGATIVE) && value2.equals(SignDomainValue.POSITIVE))) {
				newState.setValue(entry.getKey(), SignDomainValue.TOP);
				continue;
			}

			// If one of the values is bottom, the resulting value is bottom.
			if (value1.equals(SignDomainValue.BOTTOM) || value2.equals(SignDomainValue.BOTTOM)) {
				newState.setValue(entry.getKey(), SignDomainValue.BOTTOM);
				continue;
			}

			if (value1.equals(SignDomainValue.ZERO) || value2.equals(SignDomainValue.ZERO)) {
				newState.setValue(entry.getKey(), SignDomainValue.TOP);
				continue;
			}
		}

		return newState;
	}

}
