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
		return mBacking.toString();
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof VisualizationEdge) {
			return mBacking.equals(((VisualizationEdge) obj).mBacking);
		}
		return super.equals(obj);
	}

	@Override
	public int hashCode() {
		return mBacking.hashCode();
	}

}
