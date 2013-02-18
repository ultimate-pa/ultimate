/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.safetychecker.preferences;

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
	public static String NAME_ACTIVATEDUMPFORMULA	= "DumpFormulas";
	public static String NAME_DUMPPATH				= "dumpPath";
	public static String NAME_MAXSTEPNUMBER			= "maxStepNumber";
	public static String NAME_ACTIVATEEPSILON		= "epsilon";
	
	/*
	 * labels for the different preferencess
	 */

	public static String LABEL_ACTIVATEDUMPFORMULA	= "Dump interpolation problems to files";
	public static String LABEL_DUMPPATH				= "Dump interpolation problems to";
	public static String LABEL_MAXSTEPNUMBER		= "Maximum number of steps the safety checker will take";
	public static String LABEL_ACTIVATEEPSILON		= "Use Epsilon-Alternative on split edges";
	
	/*
	 * default values for the different preferences
	 */

	public static boolean	VALUE_ACTIVATEDUMPFORMULA_DEFAULT	= false;
	public static int		VALUE_MAXSTEPNUMBER_DEFAULT			= 1000; //(alex) geändert für benchmarking (nicht commiten..)
	public static int		VALUE_MAXSTEPNUMBER_MAX				= 1001;
	public static boolean	VALUE_ACTIVATEEPSILON_DEFAULT		= false;

	/*
	 * Names for the preferences concerning graph output - by alex
	 */
	
	public static String NAME_IMAGE_PATH = "imagePathPreference";
	public static String NAME_ANNOTATE_EDGES = "booleanPreference1";
	public static String NAME_ANNOTATE_NODES = "booleanPreference2";
	public static String NAME_SHOW_UNREACHABLE = "booleanPreference3";
	
	public static String LABEL_IMAGE_PATH = "&Directory for writing the graphs (empty for don't write):";
	public static String LABEL_ANNOTATE_EDGES = "&Show formulas of edges";
	public static String LABEL_ANNOTATE_NODES = "&Show formulas of nodes";
	public static String LABEL_SHOW_UNREACHABLE = "&Show unreachable nodes (by following edges against their direction)";
	
	public static String  VALUE_IMAGE_PATH = "";
	public static boolean VALUE_ANNOTATE_EDGES = false;
	public static boolean VALUE_ANNOTATE_NODES = false;
	public static boolean VALUE_SHOW_UNREACHABLE = true;
	
}
