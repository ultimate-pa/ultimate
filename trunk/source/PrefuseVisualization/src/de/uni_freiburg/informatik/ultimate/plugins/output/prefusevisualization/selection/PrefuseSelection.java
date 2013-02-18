package de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.selection;

import de.uni_freiburg.informatik.ultimate.model.IPayload;

import de.uni_freiburg.informatik.ultimate.gui.interfaces.IPayloadSelection;

/**
 * the prefuse selection event
 * 
 * @author keil
 * @version 0.0.1 
 * $LastChangedDate$
 * $LastChangedBy$
 * $LastChangedRevision$
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
	 * @see de.uni_freiburg.informatik.ultimate.gui.interfaces.IPayloadSelection#isEmpty()
	 */
	public boolean isEmpty() {
		return (this.selectedNode == null);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.gui.interfaces.IPayloadSelection#getPayload()
	 */
	public IPayload getPayload() {
		return this.selectedNode;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.gui.interfaces.IPayloadSelection#setPayload(de.uni_freiburg.informatik.ultimate.model.IPayload)
	 */
	public void setPayload(IPayload node) {
		this.selectedNode = node;
	}
}