package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngineParameters;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IFixpointEngine;

@FunctionalInterface
public interface IFixpointEngineFactory<STATE extends IAbstractState<STATE>, ACTION, VARDECL, LOC> {
	IFixpointEngine<STATE, ACTION, VARDECL, LOC>
			constructFixpointEngine(FixpointEngineParameters<STATE, ACTION, VARDECL, LOC> params);
}
