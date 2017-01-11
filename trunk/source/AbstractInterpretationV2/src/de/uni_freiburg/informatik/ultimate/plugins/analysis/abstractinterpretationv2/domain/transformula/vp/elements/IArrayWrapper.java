package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPTfState;

public interface IArrayWrapper {

	/**
	 * 
	 * @param tfState
	 * @param requestedIndices the surrounding term(s) might be interested only in some indices (typical for a select term)
	 *                        --> this field allows the arrayWrapper to return an anonymous array specially tailored to such an index set
	 *                        --> if you don't want to give requested indices, just give "null" here.
	 * @return
	 */
	Set<ArrayWithSideCondition> getArrayWithSideConditions(VPTfState tfState, Set<List<NodeIdWithSideCondition>> requestedIndices);

	/**
	 * Get the array that this wrapper is built around. (i.e. array in the innermost store term)
	 * @return
	 */
	VPTfArrayIdentifier getBaseArray();
}
