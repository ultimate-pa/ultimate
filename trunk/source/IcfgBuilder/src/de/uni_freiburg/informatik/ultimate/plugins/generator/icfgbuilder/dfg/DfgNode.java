package de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.dfg;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;

/**
 * Wrapper class of a IcfgEdge for a Data Flow Graph Node for easier Implementation.
 *
 * @author christof.schuster@gmx.de
 */
public class DfgNode {
	private final IcfgEdge mEdge;

	public DfgNode(final IcfgEdge edge) {
		mEdge = edge;
	}

	public IcfgEdge getCorrespondingDFGEdge() {
		return mEdge;
	}

	@Override
	public String toString() {
		return mEdge.toString();
	}

	@Override
	public int hashCode() {
		return Objects.hash(mEdge);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final DfgNode other = (DfgNode) obj;
		return Objects.equals(mEdge, other.mEdge);
	}

}
