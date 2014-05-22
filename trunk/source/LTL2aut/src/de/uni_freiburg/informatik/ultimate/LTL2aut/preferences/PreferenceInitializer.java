package de.uni_freiburg.informatik.ultimate.LTL2aut.preferences;

import de.uni_freiburg.informatik.ultimate.LTL2aut.Activator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;

public class PreferenceInitializer extends UltimatePreferenceInitializer {

	/*
	 * labels for the different preferencess
	 */
	public static final String LABEL_TOOLLOCATION = "Path to LTL*BA executable (LTL2BA, LTL3BA)";
	public static final String LABEL_TOOLARGUMENT = "Command line string";
	public static final String LABEL_PROPERTYFROMFILE = "Read property from file";
	public static final String LABEL_PPROPERTY = "Property to check";

	/*
	 * default values for the different preferences
	 */
	public static final String DEF_TOOLLOCATION = "";
	public static final String DEF_TOOLARGUMENT = "\"!( $1 )\"";
	public static final boolean DEF_PROPERTYFROMFILE = false;
	public static final String DEF_PPROPERTY = "[] a \n a: x > 42";

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<String>(LABEL_TOOLLOCATION, DEF_TOOLLOCATION, PreferenceType.File),
				new UltimatePreferenceItem<String>(LABEL_TOOLARGUMENT, DEF_TOOLARGUMENT, PreferenceType.String),
				new UltimatePreferenceItem<Boolean>(LABEL_PROPERTYFROMFILE, DEF_PROPERTYFROMFILE,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<String>(LABEL_PPROPERTY, DEF_PPROPERTY, PreferenceType.MultilineString) };
	}

	@Override
	protected String getPlugID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return "LTL2aut";
	}
	
	public static boolean readPropertyFromFile(){
		return new UltimatePreferenceStore(Activator.PLUGIN_ID).getBoolean(PreferenceInitializer.LABEL_PROPERTYFROMFILE);
	}
}