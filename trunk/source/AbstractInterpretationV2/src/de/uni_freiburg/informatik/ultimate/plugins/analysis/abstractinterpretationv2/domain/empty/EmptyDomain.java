package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.empty;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractStateBinaryOperator;

/**
 * This domain does exactly nothing. It can be used to test various aspects of
 * the framework.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 * @param <ACTION>
 *            Any action type.
 * @param <VARDECL>
 *            Any variable declaration.
 */
public class EmptyDomain<ACTION, VARDECL> implements
		IAbstractDomain<EmptyDomainState<ACTION, VARDECL>, ACTION, VARDECL> {

	private EmptyStateConverter<ACTION, VARDECL> mStateConverter;

	public EmptyDomain() {
		mStateConverter = new EmptyStateConverter<ACTION, VARDECL>(new EmptyDomainState<ACTION, VARDECL>());
	}

	@Override
	public IAbstractState<ACTION, VARDECL> createFreshState() {
		return new EmptyDomainState<ACTION, VARDECL>();
	}

	@Override
	public IAbstractStateBinaryOperator<ACTION, VARDECL> getWideningOperator() {
		return new EmptyOperator<>(mStateConverter);
	}

	@Override
	public IAbstractStateBinaryOperator<ACTION, VARDECL> getMergeOperator() {
		return new EmptyOperator<>(mStateConverter);
	}

	@Override
	public IAbstractPostOperator<ACTION, VARDECL> getPostOperator() {
		return new EmptyPostOperator<>(mStateConverter);
	}

	@Override
	public Class<EmptyDomainState<ACTION, VARDECL>> getAbstractStateClass() {
		return mStateConverter.getAbstractStateClass();
	}

}
