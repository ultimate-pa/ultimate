/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.kojak.preferences;

/**
 * This class saves identifier, labels, default values and in some cases
 * (RadioGroupFieldEditor) choosable values for the preference page of this
 * plugin
 * 
 * @author ermis
 * @version 0.0.3 
 * $LastChangedDate: 2008-02-09 23:14:39 +0100 (Sa, 09 Feb 2008) $
 * $LastChangedBy: ermis 
 * $LastChangedRevision: 473 $
 */
public class PreferenceValues {
	/*
	 * Names for the different preferences
	 */
	public static final String NAME_TIMEOUT 	= "timeout";
	public static String NAME_DUMPPATH			= "dumpPath";
	public static String NAME_MAXSTEPNUMBER		= "maxStepNumber";
	public static String NAME_ACTIVATEEPSILON	= "epsilon";
	public static final String NAME_LIBRARYMODE = "libmode";
	
	/*
	 * labels for the different preferences
	 */
	public static final String LABEL_TIMEOUT 	= "Timeout of Kojak\n * In seconds; default 300 sec.";
	public static String LABEL_DUMPPATH			= "Dump SMT script\n * Leave empty if no dump requested";
	public static String LABEL_MAXSTEPNUMBER	= "Step# of Kojak\n * Default is 0 means unbounded.";
	public static String LABEL_ACTIVATEEPSILON	= "Add Epsilon edges";
	public static String LABEL_LIBRARYMODE		= "Library mode on";
	
	/*
	 * default values for the different preferences
	 */
	public static final int VALUE_TIMEOUT_DEFAULT 				= 300;
	public static String	VALUE_DUMPPATH_DEFAULT				= "";
	public static int		VALUE_MAXSTEPNUMBER_DEFAULT			= 0;
	public static boolean	VALUE_ACTIVATEEPSILON_DEFAULT		= false;
	public static boolean	VALUE_LIBRARYMODE_DEFAULT			= false;
}
