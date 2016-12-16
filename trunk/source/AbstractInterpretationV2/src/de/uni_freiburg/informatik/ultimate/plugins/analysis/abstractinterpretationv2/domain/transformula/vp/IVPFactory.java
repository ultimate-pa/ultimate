package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public interface IVPFactory<T extends IVPStateOrTfState> {

	IVPStateOrTfStateBuilder<T> copy(T state);

	T getBottomState(Set<IProgramVar> variables);

	Set<VPNodeIdentifier> getFunctionNodesForArray(T resultState, VPArrayIdentifier firstArray);

	IVPStateOrTfStateBuilder<T> createEmptyStateBuilder(TransFormula tf); // TODO not so nice..
}
