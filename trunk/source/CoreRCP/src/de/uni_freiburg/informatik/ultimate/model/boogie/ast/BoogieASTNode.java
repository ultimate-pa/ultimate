package de.uni_freiburg.informatik.ultimate.model.boogie.ast;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.location.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.model.structure.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.model.structure.ISimpleAST;
import de.uni_freiburg.informatik.ultimate.model.structure.IWalkable;
import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationNode;


public class BoogieASTNode extends BasePayloadContainer implements ISimpleAST<BoogieASTNode>  {

	private static final long serialVersionUID = 5856434889026482850L;

	public BoogieASTNode(ILocation location) {
		super();

		getPayload().setLocation(location);

		if (location instanceof BoogieLocation) {
			((BoogieLocation) location).setBoogieASTNode(this);
		}
	}

	public ILocation getLocation() {
		return getPayload().getLocation();
	}

	protected BoogieASTNode createSpecialChild(String name, Object[] childs) {
		BoogieASTWrapper parent = new BoogieASTWrapper(null, name);
		for (Object obj : childs) {
			parent.getOutgoingNodes().add(createSpecialChild(obj));
		}
		return parent;
	}

	protected BoogieASTNode createSpecialChild(Object obj) {
		return new BoogieASTWrapper(null, obj);
	}
	
	@Override
	public VisualizationNode getVisualizationGraph() {
		return new VisualizationNode(this);
	}

	@Override
	public List<IWalkable> getSuccessors() {
		ArrayList<IWalkable> rtr = new ArrayList<>();
		for(BoogieASTNode node : getOutgoingNodes()){
			rtr.add(node);
		}
		return rtr;
	}

	@Override
	public List<BoogieASTNode> getOutgoingNodes() {
		return new ArrayList<BoogieASTNode>();
	}

	private class BoogieASTWrapper extends BoogieASTNode {

		private static final long serialVersionUID = 1L;
		private Object mBacking;

		public BoogieASTWrapper(ILocation location, Object backing) {
			super(location);
			mBacking = backing;
		}

		@Override
		public String toString() {
			if (mBacking != null) {
				return mBacking.toString();
			} else {
				return super.toString();
			}
		}

	}
}
