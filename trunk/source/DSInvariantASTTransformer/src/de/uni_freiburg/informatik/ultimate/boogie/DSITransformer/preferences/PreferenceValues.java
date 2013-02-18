package de.uni_freiburg.informatik.ultimate.boogie.DSITransformer.preferences;

/**
 * This class saves identifier, labels, default values and in some cases
 * (RadioGroupFieldEditor) values for the preference page of this plug-in
 * 
 * @author various
 */
public class PreferenceValues {

	/*
	 * Names for the different preferences
	 */
	public static String NAME_STRUCTURETYPE	= "structureType";
	public static String NAME_PROCEDUREID	= "structureProcID";
	public static String NAME_TRIMWRAP	= "trimAfterWrap";
	public static String NAME_ALLFUNCTIONS = "allFunctions";
	public static String NAME_LEAVEPROCEDURES = "leaveOriginalProcedures";
		
	/*
	 * labels for the different preferences
	 */

	public static String LABEL_STRUCTURETYPE = "Structure Type";
	public static String LABEL_PROCEDUREID = "New Procedure Identifier";
	public static String LABEL_TRIMWRAP = "Trim after \"$wrap\"?";
	public static String LABEL_ALLFUNCTIONS = "All methods (ignores all other options)";
	public static String LABEL_LEAVEPROCEDURES = "Don't remove original procedure declarations?";
	
	/*
	 * default values for the different preferences
	 */

	public static boolean VALUE_TRIMWRAP_DEFAULT = true;
	public static boolean VALUE_ALLFUNCTIONS_DEFAULT = false;
	public static boolean VALUE_LEAVEPROCEDURES = false;
	
}
