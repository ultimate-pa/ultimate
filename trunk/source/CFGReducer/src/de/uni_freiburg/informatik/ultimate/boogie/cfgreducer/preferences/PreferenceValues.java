package de.uni_freiburg.informatik.ultimate.boogie.cfgreducer.preferences;

public class PreferenceValues {

	/*
	 * Names for the different preferences
	 */
	public static String NAME_REDUCEGRAPH			= "ReduceGraph";
	public static String NAME_MERGEPARALLELEDGES	= "MergeParallelEdges";
	public static String NAME_SELECTEDSOLVER		= "SelectedSolver";
	public static String NAME_DUMPPATH				= "DumpPath";
	public static String NAME_IDTAGEDGES			= "IdTagEdges";
	
	/*
	 * labels for the different preferencess
	 */

	public static String LABEL_REDUCEGRAPH			= "Don't reduce graph. Just shift assumptions into edges";
	public static String LABEL_MERGEPARALLELEDGES	= "Merge parallel edges when reducing";
	public static String LABEL_SELECTEDSOLVER		= "Select solver for CFGEdge class";
	public static String LABEL_DUMPPATH				= "Dump smt files of CFGEdge class to";
	public static String LABEL_IDTAGEDGES			= "Id tag all edges";
	
	/*
	 * default values for the different preferences
	 */

	public static boolean 	VALUE_REDUCEGRAPH_DEFAULT 			= false;
	public static boolean 	VALUE_MERGEPARALLELEDGES_DEFAULT	= false;
	public static boolean 	VALUE_IDTAGEDGES_DEFAULT			= false;
	public static String	VALUE_SELECTEDSOLVER_DEFAULT		= "1";
	public static String	VALUE_DUMPPATH_DEFAULT				= "";	
}
