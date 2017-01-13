package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPTfStateBuilder;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class VpTfExtraNodeIdentifier extends VPTfNodeIdentifier {

	/**
	 * @param eqNode
	 * @param tfStateBuilder TODO: parameter seems unnecessary
	 */
	public VpTfExtraNodeIdentifier(EqNode eqNode, TfNodeInOutStatus inOutStatus) {
		super(eqNode, inOutStatus);
		assert !(eqNode instanceof EqFunctionNode);
	}

	@Override
	public VPTfArrayIdentifier getFunction() {
		assert false : "we don't introduce extraNodeIds for function nodes, right?";
		return null;
	}

	@Override
	public String toString() {
		return "VpTfTExtraNodeIdentifier: " + getEqNode().toString() + "(" + mInOutStatus + ")";
	}

	@Override
	public boolean equals(Object other) {
		if (!(other instanceof VpTfExtraNodeIdentifier)) {
			return false;
		}

		VpTfExtraNodeIdentifier otherVpThroughId = (VpTfExtraNodeIdentifier) other;
		if (otherVpThroughId.getEqNode() != this.getEqNode()) {
			return false;
		}

		
		return true;
	}

	@Override
	public int hashCode() {
		return HashUtils.hashHsieh(31, getEqNode());
	}
	
	
}
