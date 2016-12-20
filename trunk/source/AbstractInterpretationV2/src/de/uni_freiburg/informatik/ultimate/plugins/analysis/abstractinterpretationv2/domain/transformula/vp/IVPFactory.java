package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public interface IVPFactory<STATE extends IVPStateOrTfState<NODEID, ARRAYID>, NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID> {

	IVPStateOrTfStateBuilder<STATE, NODEID, ARRAYID> copy(STATE state);

	STATE getBottomState(Set<IProgramVar> variables);

	Set<NODEID> getFunctionNodesForArray(STATE resultState, ARRAYID firstArray);

	IVPStateOrTfStateBuilder<STATE, NODEID, ARRAYID> createEmptyStateBuilder(TransFormula tf); // TODO not so nice..
}
