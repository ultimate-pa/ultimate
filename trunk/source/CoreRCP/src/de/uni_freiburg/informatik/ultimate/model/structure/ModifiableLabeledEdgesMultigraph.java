package de.uni_freiburg.informatik.ultimate.model.structure;



public class ModifiableLabeledEdgesMultigraph<T extends ModifiableLabeledEdgesMultigraph<T,L>,L> extends
		BaseLabeledEdgesMultigraph<T,L> {

	private static final long serialVersionUID = -3595056576172626796L;

	/**
	 * Adds an outgoing node to the corresponding list and updates the hashmap with the edge label accordingly.
	 * @param node
	 * @param label
	 * @return true iff the list update was succesful, only then the hashmap is
	 *  updated, too.
	 */
	public boolean addOutgoingNode(T node, L label) {
		if (mOutgoingNodes.add(node)) {
			mOutgoingEdgeLabels.add(label);
			return true;
		}
		return false;
	}
	
	/**
	 * Removes an outgoing node from the corresponding list and updates the hashmap with the edge label accordingly.
	 * @param node
	 * @param label
	 * @return true iff the list update was successful, only then the hashmap is
	 *  updated, too.
	 */
	public boolean removeOutgoingNode(T node) {
		int index = mOutgoingNodes.indexOf(node);
		if (mOutgoingNodes.remove(index) != null) {
			mOutgoingEdgeLabels.remove(index);
			return true;
		}
		return false;
	}
	
	/**
	 * Adds an incoming node to the corresponding list.
	 * @param node
	 * @param label
	 * @return true iff the list update was successful.
	 */
	public boolean addIncomingNode(T node) {
		return mIncomingNodes.add(node);
	}
	
	/**
	 * Remove an incoming node from the corresponding list.
	 * @param node
	 * @param label
	 * @return true iff the list update was succesful.
	 */
	public boolean removeIncomingNode(T node) {
		return mIncomingNodes.remove(node);
	}
	
	/**
	 * Create an (non-explicit) outgoing edge to the given node with the given label.
	 * Updates the corresponding lists in the two nodes and updates the hashmap in
	 * "this".
	 * @param node
	 * @param label
	 * @return true iff the adding operations were successful, false otherwise. In
	 *  the latter case, changes already made are undone.
	 */
	public boolean connectOutgoing(T node, L label) {
		assert label != null;
		if(mOutgoingNodes.add(node)){
			if(node.mIncomingNodes.add((T) this)){
				mOutgoingEdgeLabels.add(label);
				return true;
			} else {
				mOutgoingNodes.remove(node);
				return false;
			}
		}
		return false;
	}
	
	/**
	 * Removes an (non-explicit) outgoing edge from the given node.
	 * Updates the corresponding lists in the two nodes and updates the hashmap in
	 * the node "this".
	 * @param node
	 * @param label
	 * @return true iff the adding operations were successful, false otherwise. In
	 *  the latter case, changes already made are undone.
	 */
	public boolean disconnectOutgoing(T node) {
		int index = mOutgoingNodes.indexOf(node);
		if(mOutgoingNodes.remove(index) != null) {
			if(node.mIncomingNodes.remove(this)) {
				mOutgoingEdgeLabels.remove(index);
				return true;
			} else {
				mOutgoingNodes.add(node);
				return false;
			}
		}
		return false;
	}
	
	/**
	 * Creates an (non-explicit) incoming edge from the given node with the given label.
	 * Updates the corresponding lists in the two nodes and updates the hashmap in
	 * the node given as the first argument.
	 * @param node
	 * @param label
	 * @return true iff the adding operations were successful, false otherwise. In
	 *  the latter case, changes already made are undone.
	 */
	public boolean connectIncoming(T node, L label) {
		assert label != null;
		if(mIncomingNodes.add(node)) {
			if(node.mOutgoingNodes.add((T) this)) {
				node.mOutgoingEdgeLabels.add(label);
				return true;
			} else {
				mIncomingNodes.remove(node);
				return false;
			}
		}
		return false;
	}
	
	/**
	 * Removes an (non-explicit) incoming edge from the given node.
	 * Updates the corresponding lists in the two nodes and updates the hashmap in
	 * the node given as an argument.
	 * @param node
	 * @param label
	 * @return true iff the adding operations were successful, false otherwise. In
	 *  the latter case, changes already made are undone.
	 */
	public boolean disconnectIncoming(T node) {
		if (mIncomingNodes.remove(node)) {
			int index = node.mOutgoingNodes.indexOf(this);
			if (node.mOutgoingNodes.remove(index) != null) {
				node.mOutgoingEdgeLabels.remove(index);
				return true;
			} else {
				mIncomingNodes.add(node);
				return false;
			}
		}
		return false;
	}
}
