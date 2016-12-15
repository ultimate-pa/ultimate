package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public interface IVPFactory<T extends IVPStateOrTfState> {

	IVPStateOrTfStateBuilder<T> copy(T state);

	T getBottomState(Set<IProgramVar> variables);

	IVPStateOrTfStateBuilder<T> createEmptyStateBuilder();
}
