package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.empty;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractStateBinaryOperator;

public final class EmptyOperator<ACTION, VARDECL> implements IAbstractStateBinaryOperator<ACTION, VARDECL> {

	private EmptyStateConverter<ACTION, VARDECL> mStateConverter;

	protected EmptyOperator(EmptyStateConverter<ACTION, VARDECL> stateConverter) {
		mStateConverter = stateConverter;
	}

	@Override
	public IAbstractState<ACTION, VARDECL> apply(IAbstractState<ACTION, VARDECL> first,
			IAbstractState<ACTION, VARDECL> second) {
		assert first != null;
		assert second != null;
		final EmptyDomainState<ACTION, VARDECL> firstState = mStateConverter.getCheckedState(first);
		final EmptyDomainState<ACTION, VARDECL> secondState = mStateConverter.getCheckedState(second);

		if (!firstState.hasSameVariables(secondState)) {
			throw new UnsupportedOperationException("Cannot widen or merge two states with different variables");
		}

		return new EmptyDomainState<>(firstState.getVariables(), firstState.isFixpoint() || secondState.isFixpoint());
	}
}
