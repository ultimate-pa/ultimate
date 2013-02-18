package local.stalin.gui.interfaces;

import local.stalin.model.IPayload;

import org.eclipse.jface.viewers.ISelection;

public interface IPayloadSelection extends ISelection {
	
	public IPayload getPayload();
	public void setPayload(IPayload payload);
	public boolean isEmpty();
}
