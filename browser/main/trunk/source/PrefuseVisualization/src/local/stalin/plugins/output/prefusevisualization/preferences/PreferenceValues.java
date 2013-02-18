package local.stalin.plugins.output.prefusevisualization.preferences;

import local.stalin.plugins.output.prefusevisualization.Activator;

import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

/**
 * This class saves choosable values for the preference page of this plugin
 * 
 * @author keil
 * @version 0.0.1 
 * $LastChangedDate: 2008-03-07 13:50:06 +0100 (Fr, 07 Mrz 2008) $
 * $LastChangedBy: keilr $
 * $LastChangedRevision: 495 $
 */
public class PreferenceValues {

	public static ScopedPreferenceStore Preference = new ScopedPreferenceStore(
			new ConfigurationScope(), Activator.PLUGIN_ID);

	/*
	 * Names for the different preferences
	 */
	public static String NAME_DISPLAYCHOOSERECUTABLE = "displayChooser";
	public static String NAME_STANDARDDISPLAY = "defaultDisplay";

	public static String NAME_NODESTYLECOLOR = "NodeStyleColor";
	public static String NAME_NODEMARKCOLOR = "NodeMarkColor";
	public static String NAME_NODEOVERCOLOR = "NodeOverColor";
	public static String NAME_TEXTSTYLECOLOR_LEAF = "TextStyleColor (Leaf)";
	public static String NAME_TEXTSTYLECOLOR_UNDEFIENEDTOKEN = "TextStyleColor (undefiend Token)";
	public static String NAME_TEXTSTYLECOLOR_TOKEN = "TextStyleColor (Token)";
	public static String NAME_TEXTMARKCOLOR = "TextMarkColor";
	public static String NAME_TEXTOVERCOLOR = "TextOverColor";
	public static String NAME_EDGESTYLECOLOR = "EdgeStyleColor";

	public static String NAME_NODEFONT = "NodeFont";

	/*
	 * default values for the different preferences
	 */
	public static boolean VALUE_DISPLAYCHOOSERECUTABLE_DEFAULT = true;
	public static String VALUE_STANDARDDISPLAY_DEFAULT = "vertical TreeView (complete)";

	public static RGB VALUE_NODESTYLECOLOR_DEFAULT = new RGB(255, 255, 255);
	public static RGB VALUE_NODEMARKCOLOR_DEFAULT = new RGB(255, 69, 0);
	public static RGB VALUE_NODEOVERCOLOR_DEFAULT = new RGB(255, 255, 255);

	public static RGB VALUE_TEXTSTYLECOLOR_LEAF_DEFAULT = new RGB(51, 153, 0);
	public static RGB VALUE_TEXTSTYLECOLOR_UNDEFIENEDTOKEN_DEFAULT = new RGB(
			102, 51, 204);
	public static RGB VALUE_TEXTSTYLECOLOR_TOKEN_DEFAULT = new RGB(178, 34, 34);

	public static RGB VALUE_TEXTMARKCOLOR_DEFAULT = new RGB(0, 0, 0);
	public static RGB VALUE_TEXTOVERCOLOR_DEFAULT = new RGB(255, 69, 0);
	public static RGB VALUE_EDGESTYLECOLOR_DEFAULT = new RGB(200, 200, 200);

	public static FontData VALUE_NODEFONT_DEFAULT = new FontData("Tahoma", 10,
			0);

	/*
	 * labels for the different preferencess
	 */
	public static String LABEL_DISPLAYCHOOSERECUTABLE = "Enable Displaychooser";
	public static String LABEL_STANDARDDISPLAY = "Standard Display";

	public static String LABEL_NODESTYLECOLOR = "NodeStyleColor";
	public static String LABEL_NODEMARKCOLOR = "NodeMarkColor";
	public static String LABEL_NODEOVERCOLOR = "NodeOverColor";
	public static String LABEL_TEXTSTYLECOLOR_LEAF = "TextStyleColor (Leaf)";
	public static String LABEL_TEXTSTYLECOLOR_UNDEFIENEDTOKEN = "TextStyleColor (undefiend Token)";
	public static String LABEL_TEXTSTYLECOLOR_TOKEN = "TextStyleColor (Token)";
	public static String LABEL_TEXTMARKCOLOR = "TextMarkColor";
	public static String LABEL_TEXTOVERCOLOR = "TextOverColor";
	public static String LABEL_EDGESTYLECOLOR = "EdgeStyleColor";

	public static String LABEL_NODEFONT = "NodeFont";

	/*
	 * choosable values
	 */
	public static String[][] VALUES_DISPLAYCHOOSERECUTABLE = new String[][] {
			{ "Enabled", "true" }, { "Disabeld", "false" } };

	public static String[][] VALUES_STANDARDDISPLAY = new String[][] {
			{ "horizontal TreeView (partial)", "horizontal TreeView (partial)" },
			{ "horizontal TreeView (complete)",
					"horizontal TreeView (complete)" },
			{ "vertical TreeView (partial)", "vertical TreeView (partial)" },
			{ "vertical TreeView (complete)", "vertical TreeView (complete)" },
			{ "RadialGraphView (complete)", "RadialGraphView (complete)" },
			{ "RadialGraphView (rotate)", "RadialGraphView (rotate)" } };

	/**
	 * loads the default values to the scope
	 */
	public static void initializeDefaultPreferences() {

		Preference.setDefault(PreferenceValues.NAME_DISPLAYCHOOSERECUTABLE,
				PreferenceValues.VALUE_DISPLAYCHOOSERECUTABLE_DEFAULT);
		Preference.setDefault(PreferenceValues.NAME_STANDARDDISPLAY,
				PreferenceValues.VALUE_STANDARDDISPLAY_DEFAULT);
		PreferenceConverter.setDefault((IPreferenceStore) Preference,
				PreferenceValues.NAME_NODESTYLECOLOR,
				PreferenceValues.VALUE_NODESTYLECOLOR_DEFAULT);
		PreferenceConverter.setDefault(Preference,
				PreferenceValues.NAME_NODEMARKCOLOR,
				PreferenceValues.VALUE_NODEMARKCOLOR_DEFAULT);
		PreferenceConverter.setDefault(Preference,
				PreferenceValues.NAME_NODEOVERCOLOR,
				PreferenceValues.VALUE_NODEOVERCOLOR_DEFAULT);
		PreferenceConverter.setDefault(Preference,
				PreferenceValues.NAME_TEXTSTYLECOLOR_LEAF,
				PreferenceValues.VALUE_TEXTSTYLECOLOR_LEAF_DEFAULT);
		PreferenceConverter.setDefault(Preference,
				PreferenceValues.NAME_TEXTSTYLECOLOR_UNDEFIENEDTOKEN,
				PreferenceValues.VALUE_TEXTSTYLECOLOR_UNDEFIENEDTOKEN_DEFAULT);
		PreferenceConverter.setDefault(Preference,
				PreferenceValues.NAME_TEXTSTYLECOLOR_TOKEN,
				PreferenceValues.VALUE_TEXTSTYLECOLOR_TOKEN_DEFAULT);
		PreferenceConverter.setDefault(Preference,
				PreferenceValues.NAME_TEXTMARKCOLOR,
				PreferenceValues.VALUE_TEXTMARKCOLOR_DEFAULT);
		PreferenceConverter.setDefault(Preference,
				PreferenceValues.NAME_TEXTOVERCOLOR,
				PreferenceValues.VALUE_TEXTOVERCOLOR_DEFAULT);
		PreferenceConverter.setDefault(Preference,
				PreferenceValues.NAME_EDGESTYLECOLOR,
				PreferenceValues.VALUE_EDGESTYLECOLOR_DEFAULT);
		PreferenceConverter.setDefault(Preference,
				PreferenceValues.NAME_NODEFONT,
				PreferenceValues.VALUE_NODEFONT_DEFAULT);
	}
}