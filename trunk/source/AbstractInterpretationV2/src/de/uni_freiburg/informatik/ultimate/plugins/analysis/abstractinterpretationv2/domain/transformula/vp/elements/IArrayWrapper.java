package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPTfState;

public interface IArrayWrapper {

	Set<ArrayWithSideCondition> getArrayWithSideConditions(VPTfState tfState);

}
