package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.compounddomain;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractState;

@SuppressWarnings("rawtypes")
public interface IRefinement {
	void refine(IAbstractState a, IAbstractState b);
}
