/**
 * 
 */
package local.stalin.plugins.safetychecker.preferences;

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
	
	/*
	 * labels for the different preferencess
	 */

	public static String LABEL_ACTIVATEDUMPFORMULA	= "Dump interpolation problems to files";
	public static String LABEL_DUMPPATH				= "Dump interpolation problems to";
	public static String LABEL_MAXSTEPNUMBER		= "Maximum number of steps the safety checker will take";
	
	/*
	 * default values for the different preferences
	 */

	public static boolean	VALUE_ACTIVATEDUMPFORMULA_DEFAULT	= false;
	public static int		VALUE_MAXSTEPNUMBER_DEFAULT			= 100;
	public static int		VALUE_MAXSTEPNUMBER_MAX				= 1001;
	
	
	
}
