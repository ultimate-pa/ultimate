package de.uni_freiburg.informatik.ultimate.model.structure;



public class ModifiableLabeledEdgesMultigraph<T extends ModifiableLabeledEdgesMultigraph<T,L>,L> extends
		BaseLabeledEdgesMultigraph<T,L> {

	
	public boolean addOutgoingNode(T node, L label) {
		if (node != null) {
			mOutgoingNodes.add(node);
			mOutgoingEdgeLabels.put(node, label);
			return true;
		}
		return false;
	}

	public void removeOutgoingNode(T node) {
		mOutgoingNodes.remove(node);
		mOutgoingEdgeLabels.remove(node);
	}
	
	
	public boolean connectOutgoing(T node, L label) {
		if(mOutgoingNodes.add(node)){
			mOutgoingEdgeLabels.put(node, label);
			if(node.mIncomingNodes.add((T) this)){
				return true;
			} else {
				mOutgoingEdgeLabels.remove(node);
				mOutgoingNodes.remove(node);
				return false;
			}
		}
		return false;
	}

	public void disconnectOutgoing(T node) {
		mOutgoingNodes.remove(node);
		mOutgoingEdgeLabels.remove(node);
		node.mIncomingNodes.remove(this);
	}
	
	public void connectIncoming(T node, L label) {
		this.mIncomingNodes.add(node);
		node.mOutgoingEdgeLabels.put(node, label);
		node.mOutgoingNodes.add(this);
	}

	public void disconnectIncoming(T node) {
		mIncomingNodes.remove(node);
		node.mOutgoingNodes.remove(this);
		node.mOutgoingEdgeLabels.remove(this);
	}
	
}
