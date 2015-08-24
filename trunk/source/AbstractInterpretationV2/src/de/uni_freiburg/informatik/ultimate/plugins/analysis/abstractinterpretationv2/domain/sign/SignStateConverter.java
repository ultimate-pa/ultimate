package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;

/**
 * Checks whether a given IAbstractState is a state of the SignDomain.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 * @param <ACTION>
 *            Any action.
 * @param <VARDECL>
 *            Any variable declaration.
 */
public class SignStateConverter<ACTION, VARDECL> {
	private final Class<SignDomainState<ACTION, VARDECL>> mStateType;

	@SuppressWarnings("unchecked")
	protected SignStateConverter(SignDomainState<ACTION, VARDECL> sampleState) {
		mStateType = (Class<SignDomainState<ACTION, VARDECL>>) sampleState.getClass();
	}

	/**
	 * Throws an exception if the given state cannot be converted into a SignDomainState.
	 * 
	 * @param state
	 *            The state to be converted into a SignDomainState.
	 * @return Returns the given IAbstractState converted to a SignDomainState.
	 */
	protected SignDomainState<ACTION, VARDECL> getCheckedState(IAbstractState<ACTION, VARDECL> state) {
		if (!(mStateType.isInstance(state))) {
			throw new IllegalArgumentException("SignDomain can only process SignDomainState types as abstract states.");
		}
		return (SignDomainState<ACTION, VARDECL>) state;
	}
	
	protected Class<SignDomainState<ACTION, VARDECL>> getAbstractStateClass() {
		return mStateType;
	}
}
