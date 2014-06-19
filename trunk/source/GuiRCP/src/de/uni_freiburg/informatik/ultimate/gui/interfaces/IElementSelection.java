package de.uni_freiburg.informatik.ultimate.gui.interfaces;

import de.uni_freiburg.informatik.ultimate.model.IElement;

import org.eclipse.jface.viewers.ISelection;

public interface IElementSelection extends ISelection {
	
	public IElement getElement();
	public void setElement(IElement element);
}
