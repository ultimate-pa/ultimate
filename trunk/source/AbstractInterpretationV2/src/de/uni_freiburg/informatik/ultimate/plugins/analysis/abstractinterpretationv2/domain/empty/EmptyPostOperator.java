package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.empty;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 * @param <ACTION>
 * @param <VARDECL>
 */
public final class EmptyPostOperator<ACTION, VARDECL> implements IAbstractPostOperator<ACTION, VARDECL> {

	private EmptyStateConverter<ACTION, VARDECL> mStateConverter;

	protected EmptyPostOperator(EmptyStateConverter<ACTION, VARDECL> stateConverter) {
		mStateConverter = stateConverter;
	}

	@Override
	public IAbstractState<ACTION, VARDECL> apply(IAbstractState<ACTION, VARDECL> oldstate, ACTION concrete) {
		final EmptyDomainState<ACTION, VARDECL> concreteOldState = mStateConverter.getCheckedState(oldstate);
		return new EmptyDomainState<>(new HashMap<>(concreteOldState.getVariables()), false);
	}

}