package de.uni_freiburg.informatik.ultimate.ltl2aut.never2nwa;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableMultigraphEdge;

final class NWAVisualizationEdge<NWAVertex, NWAEdge> extends
		ModifiableMultigraphEdge<NWAVisualizationNode<NWAVertex, NWAEdge>, NWAVisualizationEdge<NWAVertex, NWAEdge>, NWAVertex, NWAEdge> {

	@Override
	public int hashCode() {
		return Objects.hash(mNWAEdge);
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
		final NWAVisualizationEdge other = (NWAVisualizationEdge) obj;
		if (mNWAEdge == null) {
			if (other.mNWAEdge != null) {
				return false;
			}
		} else if (!mNWAEdge.equals(other.mNWAEdge)) {
			return false;
		}
		return true;
	}

	private static final long serialVersionUID = 1L;
	private final NWAEdge mNWAEdge;

	protected NWAVisualizationEdge(final NWAVisualizationNode<NWAVertex, NWAEdge> source,
			final NWAVisualizationNode<NWAVertex, NWAEdge> target, final NWAEdge nwaEdge) {
		super(source, target);
		mNWAEdge = nwaEdge;
	}

	@Override
	public String toString() {
		if (mNWAEdge != null) {
			return mNWAEdge.toString();
		}
		return "NULL";
	}

	@Override
	public NWAEdge getLabel() {
		return mNWAEdge;
	}
}
