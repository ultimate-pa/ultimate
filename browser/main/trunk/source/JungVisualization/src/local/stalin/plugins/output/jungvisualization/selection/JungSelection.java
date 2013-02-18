package local.stalin.plugins.output.jungvisualization.selection;

import local.stalin.gui.interfaces.IPayloadSelection;
import local.stalin.model.IPayload;

/**
 * Privides access to the payload of nodes.
 * @see {@link IPayloadSelection}
 * @author lena
 *
 */
public class JungSelection implements IPayloadSelection {
	
	private IPayload selectedNodePayload;
	
	
	public JungSelection() {
		this.selectedNodePayload = null;
	}

	@Override
	public IPayload getPayload() {
		return this.selectedNodePayload;
		
	}

	@Override
	public boolean isEmpty() {
		return (this.selectedNodePayload == null);
	}

	@Override
	public void setPayload(IPayload payload) {
		this.selectedNodePayload = payload;
	}

}
