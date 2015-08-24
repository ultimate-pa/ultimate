package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;

/**
 * Checks whether a given {@link IAbstractState} is a state of the IntervalDomain.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 * @param <T>
 * @param <ACTION>
 * @param <VARDECL>
 */
public class IntervalStateConverter<ACTION, VARDECL> {
	private final Class<IntervalDomainState<ACTION, VARDECL>> mStateType;

	@SuppressWarnings("unchecked")
	protected IntervalStateConverter(IntervalDomainState<ACTION, VARDECL> sampleState) {
		mStateType = (Class<IntervalDomainState<ACTION, VARDECL>>) sampleState.getClass();
	}

	public IntervalDomainState<ACTION, VARDECL> getCheckedState(IAbstractState<ACTION, VARDECL> state) {
		if (!(mStateType.isInstance(state))) {
			throw new IllegalArgumentException(
			        "The interval domain can only process IntervalDomainState types as abstract states.");
		}

		return (IntervalDomainState<ACTION, VARDECL>) state;
	}

	protected Class<IntervalDomainState<ACTION, VARDECL>> getAbstractStateClass() {
		return mStateType;
	}
}
