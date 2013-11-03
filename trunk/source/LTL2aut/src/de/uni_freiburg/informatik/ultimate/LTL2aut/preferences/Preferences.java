package de.uni_freiburg.informatik.ultimate.LTL2aut.preferences;

import java.io.File;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;

public class Preferences {

	private final String toolLocation;
	private final String toolArgs;
	
	private UltimatePreferenceStore prefs;
	
	public Preferences(){
		
		this.toolLocation = prefs.getString(PreferenceInitializer.LABEL_TOOLLOCATION,
				PreferenceInitializer.DEF_TOOLLOCATION);
		this.toolArgs = prefs.getString(PreferenceInitializer.LABEL_TOOLARGUMENT,
				PreferenceInitializer.DEF_TOOLARGUMENT);
		
	}
	
	public String getToolLocation()
	{
		return this.prefs.getString(PreferenceInitializer.LABEL_TOOLLOCATION);
	}
	
	public String getToolArgs()
	{
		return this.prefs.getString(PreferenceInitializer.LABEL_TOOLARGUMENT);
	}
}
