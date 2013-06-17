package de.uni_freiburg.informatik.ultimate.plugins.errorlocationgenerator.preferences;

public class PreferenceValues {

	/*
	 * Names for the different preferences
	 */
	public static String NAME_CHECKVALIDITYOFERROREDGE			= "CheckValiditityOfErrorEdge";
	public static String NAME_CHECKFORDEADCODE					= "CheckForDeadCode";
	public static String NAME_CHECKREACHABILITY					= "CheckReachability";
	
	/*
	 * labels for the different preferences
	 */

	public static String LABEL_CHECKVALIDITYOFERROREDGE			= "Check Validitity of Error Edge before appending Error Locations to Graph.";
	public static String LABEL_CHECKFORDEADCODE					= "Dead Code Analysis ( Checks which Edges can be taken. Not tested in current Version!)";
	public static String LABEL_CHECKREACHABILITY				= "Check Reachability of each Node (Used for Hybrid Systems. Not Dead Code Analysis!)";
	
	/*
	 * default values for the different preferences
	 */

	public static boolean 	VALUE_CHECKVALIDITYOFERROREDGE_DEFAULT 			= false;
	public static boolean 	VALUE_CHECKFORDEADCODE_DEFAULT 					= false;
	public static boolean 	VALUE_CHECKREACHABILITY_DEFAULT 				= false;
}
