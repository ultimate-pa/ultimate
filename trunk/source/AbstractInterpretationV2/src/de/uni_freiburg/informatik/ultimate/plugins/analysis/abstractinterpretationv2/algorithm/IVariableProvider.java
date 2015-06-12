package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;

public interface IVariableProvider<ACTION, VARDECL> {
	
	IAbstractState<ACTION, VARDECL> defineVariablesPre(ACTION current, IAbstractState<ACTION, VARDECL> state);
	
	IAbstractState<ACTION, VARDECL> defineVariablesPost(ACTION current, IAbstractState<ACTION, VARDECL> state);
	
}
