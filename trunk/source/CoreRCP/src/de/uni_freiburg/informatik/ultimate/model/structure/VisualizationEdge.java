package de.uni_freiburg.informatik.ultimate.model.structure;

import de.uni_freiburg.informatik.ultimate.model.IPayload;

/***
 * 
 * This class represents the edges for the Ultimate visualization structure. For
 * more details, see {@link VisualizationNode}.
 * 
 * @author dietsch
 * 
 * @see VisualizationNode
 * @see BaseMultigraphEdge
 */
public final class VisualizationEdge extends
		BaseMultigraphEdge<VisualizationNode, VisualizationEdge> {

	protected Object mBacking;

	protected VisualizationEdge(VisualizationNode source,
			VisualizationNode target, IPayload payload, Object backing) {
		super(source, target, payload);
		mBacking = backing;
	}

	protected VisualizationEdge(VisualizationNode source,
			VisualizationNode target, Object backing) {
		super(source, target);
		mBacking = backing;
	}

	private static final long serialVersionUID = 1L;

	@Override
	public String toString() {
		if (mBacking == null) {
			return "";
		} else {

			return mBacking.toString();
		}
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof VisualizationEdge) {
			VisualizationEdge other = (VisualizationEdge) obj;
			if (mBacking == null && other.mBacking == null) {
				return super.equals(obj);
			} else if (mBacking == null) {
				return false;
			} else {
				return mBacking.equals(other.mBacking);
			}
		}
		return super.equals(obj);
	}

	@Override
	public int hashCode() {
		if (mBacking == null) {
			return super.hashCode();
		} else {
			return mBacking.hashCode();
		}
	}

}
