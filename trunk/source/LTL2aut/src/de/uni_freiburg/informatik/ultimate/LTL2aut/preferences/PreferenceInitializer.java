package de.uni_freiburg.informatik.ultimate.LTL2aut.preferences;

import java.io.File;

import de.uni_freiburg.informatik.ultimate.LTL2aut.Activator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;

public class PreferenceInitializer extends UltimatePreferenceInitializer {
	

	/*
	 * labels for the different preferencess
	 */
	public static final String LABEL_TOOLLOCATION = "Path to ltl->ba tool (LTL2BA, LTL3BA) :";
	public static final String LABEL_TOOLARGUMENT = "Command line string:";
	public static final String LABEL_PPROPERTY = "Property to check:";


	/*
	 * default values for the different preferences
	 */
	public static final String DEF_TOOLLOCATION = "./";
	public static final String DEF_TOOLARGUMENT = " -f \"!( $1 )\"";
	public static final String DEF_PPROPERTY = "[] a \n a: x > 42";
	

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				//TODO: Make label for old explaination of the items.
				
				new UltimatePreferenceItem<String>(this.LABEL_TOOLLOCATION, 
						this.DEF_TOOLLOCATION, PreferenceType.String),
				new UltimatePreferenceItem<String>(this.LABEL_TOOLARGUMENT,
						this.DEF_TOOLARGUMENT, PreferenceType.String),
				new UltimatePreferenceItem<String>(this.LABEL_PPROPERTY,
						this.DEF_PPROPERTY, PreferenceType.String)
		};
	}

	@Override
	protected String getPlugID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return "LTL2aut";
	}




}