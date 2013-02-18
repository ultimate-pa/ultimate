package local.stalin.plugins.output.prefusevisualization.gui;

import java.awt.Font;

import local.stalin.plugins.output.prefusevisualization.preferences.PreferenceValues;

import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import prefuse.util.FontLib;

/**
 * specifies the Font of the node
 * 
 * @author keil
 * @version 0.0.1 
 * $LastChangedDate: 2008-03-07 13:50:06 +0100 (Fr, 07 Mrz 2008) $
 * $LastChangedBy: keilr $
 * $LastChangedRevision: 495 $ 
 */
public class PrefuseFontSelection {

	private ScopedPreferenceStore preference = PreferenceValues.Preference;

	/**
	 * @return the standart Nodefont
	 */
	public Font getNodeFont() {
		FontData fontData = PreferenceConverter.getFontData(preference,
				PreferenceValues.NAME_NODEFONT);
		return FontLib.getFont(fontData.getName(), fontData.getHeight());
	}

	public int getDistanceFaktor() {
		FontData fontData = PreferenceConverter.getFontData(preference,
				PreferenceValues.NAME_NODEFONT);
		return fontData.getHeight();
	}
}