package de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.actions;

import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.gui.PrefuseColorSelection;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.gui.PrefusePanel;
import prefuse.action.assignment.ColorAction;
import prefuse.visual.VisualItem;

/**
 * manage the text color of an node
 * 
 * @author keil
 * @version 0.0.1 
 * $LastChangedDate$
 * $LastChangedBy$
 * $LastChangedRevision$
 */
public class TextMarkAction extends ColorAction {

	private PrefuseColorSelection ipcs = new PrefuseColorSelection();

	/**
	 * @param group
	 */
	public TextMarkAction(String group) {
		super(group, VisualItem.TEXTCOLOR);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see prefuse.action.assignment.ColorAction#getColor(prefuse.visual.VisualItem)
	 */
	public int getColor(VisualItem item) {
		if (PrefusePanel.getLastClickedItem() == item)
			return ipcs.getTextMarkColor(item.getSourceTuple()
					.getString("name"));
		else
			return ipcs.getTextStyleColor(item.getSourceTuple().getString(
					"name"));
	}
}