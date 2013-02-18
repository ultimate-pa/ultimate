package local.stalin.plugins.output.prefusevisualization.gui;

import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import prefuse.util.ColorLib;

import local.stalin.plugins.Constants;

import local.stalin.plugins.output.prefusevisualization.*;
import local.stalin.plugins.output.prefusevisualization.preferences.PreferenceValues;

/**
 * specifies the color of the node ant the nodetext in reference to his acion
 * and uid
 * 
 * @author keil
 * @version 0.0.1 
 * $LastChangedDate: 2008-03-16 12:54:00 +0100 (So, 16. Mär 2008) $
 * $LastChangedBy: keilr $
 * $LastChangedRevision: 501 $  
 */
public class PrefuseColorSelection {

	private ScopedPreferenceStore preference = PreferenceValues.Preference;

	/**
	 * standard node color
	 * 
	 * @param label
	 *            label of the selected item
	 * @return rgb value
	 */
	public int getNodeStyleColor(String label) {

		RGB color = PreferenceConverter.getColor(preference,
				PreferenceValues.NAME_NODESTYLECOLOR);
		return ColorLib.rgb(color.red, color.green, color.blue);
	}

	/**
	 * color of n marked node
	 * 
	 * @param label
	 *            label of the selected item
	 * @return rgb value
	 */
	public int getNodeMarkColor(String label) {
		RGB color = PreferenceConverter.getColor(preference,
				PreferenceValues.NAME_NODEMARKCOLOR);
		return ColorLib.rgb(color.red, color.green, color.blue);
	}

	/**
	 * hover color of an node
	 * 
	 * @param label
	 *            label of the selected item
	 * @return rgb value
	 */
	public int getNodeOverColor(String label) {
		RGB color = PreferenceConverter.getColor(preference,
				PreferenceValues.NAME_NODEOVERCOLOR);
		return ColorLib.rgb(color.red, color.green, color.blue);
	}

	/**
	 * standard text color
	 * 
	 * @param label
	 *            label of the selected item
	 * @return rgb value
	 */
	public int getTextStyleColor(String label) {
		if (PrefuseVisualization.getActiveTokenMap().get(label) == null) {
			RGB color = PreferenceConverter.getColor(preference,
					PreferenceValues.NAME_TEXTSTYLECOLOR_LEAF);
			return ColorLib.rgb(color.red, color.green, color.blue);
		}
		// some Node: does not have a mapping to the universal token list
		else if (PrefuseVisualization.getActiveTokenMap().get(label).equals(
				Constants.getTokenUndefined())) {
			RGB color = PreferenceConverter.getColor(preference,
					PreferenceValues.NAME_TEXTSTYLECOLOR_UNDEFIENEDTOKEN);
			return ColorLib.rgb(color.red, color.green, color.blue);
		}
		// a node which has a mapping to the universal tree
		else {
			RGB color = PreferenceConverter.getColor(preference,
					PreferenceValues.NAME_TEXTSTYLECOLOR_TOKEN);
			return ColorLib.rgb(color.red, color.green, color.blue);
		}
	}

	/**
	 * color of marked text
	 * 
	 * @param label
	 *            label of the selected item
	 * @return rgb value
	 */
	public int getTextMarkColor(String label) {
		RGB color = PreferenceConverter.getColor(preference,
				PreferenceValues.NAME_TEXTMARKCOLOR);
		return ColorLib.rgb(color.red, color.green, color.blue);
	}

	/**
	 * hover color of text value
	 * 
	 * @param label
	 *            label of the selected item
	 * @return rgb value
	 */
	public int getTextOverColor(String label) {
		RGB color = PreferenceConverter.getColor(preference,
				PreferenceValues.NAME_TEXTOVERCOLOR);
		return ColorLib.rgb(color.red, color.green, color.blue);
	}

	/**
	 * standart colorvalue if edges
	 * 
	 * @return
	 */
	public int getEdgeStyleColor() {
		RGB color = PreferenceConverter.getColor(preference,
				PreferenceValues.NAME_EDGESTYLECOLOR);
		return ColorLib.rgb(color.red, color.green, color.blue);
	}
}