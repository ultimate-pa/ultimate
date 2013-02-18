package local.stalin.plugins.output.prefusevisualization.selection;

import local.stalin.model.IPayload;

import local.stalin.gui.interfaces.IPayloadSelection;

/**
 * the prefuse selection event
 * 
 * @author keil
 * @version 0.0.1 
 * $LastChangedDate: 2008-03-16 12:54:00 +0100 (So, 16. Mär 2008) $
 * $LastChangedBy: keilr $
 * $LastChangedRevision: 501 $
 */
public class PrefuseSelection implements IPayloadSelection {

	private IPayload selectedNode;

	/**
	 * Creates an Prefuse Selection. This Selection is to fire an Selection
	 * Event for NodeView in the PrefusePanel
	 */
	public PrefuseSelection() {
		this.selectedNode = null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see local.stalin.gui.interfaces.IPayloadSelection#isEmpty()
	 */
	public boolean isEmpty() {
		return (this.selectedNode == null);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see local.stalin.gui.interfaces.IPayloadSelection#getPayload()
	 */
	public IPayload getPayload() {
		return this.selectedNode;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see local.stalin.gui.interfaces.IPayloadSelection#setPayload(local.stalin.model.IPayload)
	 */
	public void setPayload(IPayload node) {
		this.selectedNode = node;
	}
}