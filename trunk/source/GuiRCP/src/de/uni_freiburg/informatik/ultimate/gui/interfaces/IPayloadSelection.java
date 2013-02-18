package de.uni_freiburg.informatik.ultimate.gui.interfaces;

import de.uni_freiburg.informatik.ultimate.model.IPayload;

import org.eclipse.jface.viewers.ISelection;

public interface IPayloadSelection extends ISelection {
	
	public IPayload getPayload();
	public void setPayload(IPayload payload);
	public boolean isEmpty();
}
