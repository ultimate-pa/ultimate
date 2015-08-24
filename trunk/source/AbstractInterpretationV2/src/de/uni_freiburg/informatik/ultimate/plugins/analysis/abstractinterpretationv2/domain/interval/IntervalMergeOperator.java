package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractStateBinaryOperator;

public class IntervalMergeOperator<ACTION, VARDECL> implements IAbstractStateBinaryOperator<ACTION, VARDECL> {

	private IntervalStateConverter<ACTION, VARDECL> mStateConverter;

	protected IntervalMergeOperator(IntervalStateConverter<ACTION, VARDECL> stateConverter) {
		mStateConverter = stateConverter;
	}

	/**
	 * Merges two {@link IntervalState}s, first and second, into one new abstract state. All variables that occur in
	 * first must also occur in second.
	 */
	@Override
	public IAbstractState<ACTION, VARDECL> apply(IAbstractState<ACTION, VARDECL> first,
	        IAbstractState<ACTION, VARDECL> second) {
		assert first != null;
		assert second != null;

		final IntervalDomainState<ACTION, VARDECL> firstState = mStateConverter.getCheckedState(first);
		final IntervalDomainState<ACTION, VARDECL> secondState = mStateConverter.getCheckedState(second);

		if (!firstState.hasSameVariables(secondState)) {
			throw new UnsupportedOperationException(
			        "Cannot merge the two states as their sets of variables in the states are disjoint.");
		}

		IntervalDomainState<ACTION, VARDECL> newState = (IntervalDomainState<ACTION, VARDECL>) first.copy();

		final Map<String, VARDECL> variables = firstState.getVariables();
		final Map<String, IntervalDomainValue> firstValues = firstState.getValues();
		final Map<String, IntervalDomainValue> secondValues = secondState.getValues();

		for (Entry<String, VARDECL> entry : variables.entrySet()) {
			IntervalDomainValue value1 = firstValues.get(entry.getKey());
			IntervalDomainValue value2 = secondValues.get(entry.getKey());

			newState.setValue(entry.getKey(), computeMergedValue(value1, value2));
		}

		return null;
	}

	/**
	 * Computes the merger of two {@link IntervalDomainValue}s.
	 * 
	 * @param value1
	 * @param value2
	 * @return
	 */
	private IntervalDomainValue computeMergedValue(IntervalDomainValue value1, IntervalDomainValue value2) {
		if (value1.equals(value2.getResult())) {
			return value1;
		}

		if (value1.isBottom() || value2.isBottom()) {
			return new IntervalDomainValue(true);
		}

		IntervalValue lower = new IntervalValue();
		IntervalValue upper = new IntervalValue();

		if (value1.getLower().compareTo(value2.getLower()) < 0) {
			lower = new IntervalValue(value1.getLower().getValue());
		} else {
			lower = new IntervalValue(value2.getLower().getValue());
		}

		return new IntervalDomainValue(lower, upper);
	}

}
