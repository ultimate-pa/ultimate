package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.selection;

import de.uni_freiburg.informatik.ultimate.gui.interfaces.IElementSelection;
import de.uni_freiburg.informatik.ultimate.model.IElement;

/**
 * Provides access to nodes.
 * @see {@link IElementSelection}
 * @author lena
 *
 */
public class JungSelection implements IElementSelection {
	
	private IElement mSelectedNodePayload;
	
	
	public JungSelection() {
		mSelectedNodePayload = null;
	}

	@Override
	public IElement getElement() {
		return mSelectedNodePayload;
		
	}

	@Override
	public boolean isEmpty() {
		return (mSelectedNodePayload == null);
	}

	@Override
	public void setElement(IElement payload) {
		mSelectedNodePayload = payload;
	}

}
