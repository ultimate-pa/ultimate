package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;

public interface IAbstractStateStorage<ACTION, VARDECL> {

	Collection<IAbstractState<ACTION, VARDECL>> getAbstractPreStates(ACTION transition);

	Collection<IAbstractState<ACTION, VARDECL>> getAbstractPostStates(ACTION transition);

	IAbstractState<ACTION, VARDECL> getCurrentAbstractPreState(ACTION transition);

	IAbstractState<ACTION, VARDECL> getCurrentAbstractPostState(ACTION transition);

	void addAbstractPreState(ACTION transition, IAbstractState<ACTION, VARDECL> state);

	void addAbstractPostState(ACTION transition, IAbstractState<ACTION, VARDECL> state);

	void setPostStateIsFixpoint(ACTION transition, IAbstractState<ACTION, VARDECL> state, boolean value);

}
