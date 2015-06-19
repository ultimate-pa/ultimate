package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.empty;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;

public class EmptyStateConverter<ACTION, VARDECL> {
	private Class<EmptyDomainState<ACTION, VARDECL>> mStateType;

	@SuppressWarnings("unchecked")
	protected EmptyStateConverter(EmptyDomainState<ACTION, VARDECL> sampleState) {
		mStateType = (Class<EmptyDomainState<ACTION, VARDECL>>) sampleState.getClass();
	}

	public EmptyDomainState<ACTION, VARDECL> getCheckedState(IAbstractState<ACTION, VARDECL> state) {
		if (!(mStateType.isInstance(state))) {
			throw new IllegalArgumentException("EmptyDomain can only process EmptyDomainState as abstract state");
		}
		return (EmptyDomainState<ACTION, VARDECL>) state;
	}
	
	public Class<EmptyDomainState<ACTION, VARDECL>> getAbstractStateClass(){
		return mStateType;
	}
}
