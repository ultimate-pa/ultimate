package local.stalin.boogie.cfgreducer.preferences;

public class PreferenceValues {

	/*
	 * Names for the different preferences
	 */
	public static String NAME_REDUCEGRAPH			= "ReduceGraph";
	public static String NAME_MERGEPARALLELEDGES	= "MergeParallelEdges";
	
	/*
	 * labels for the different preferencess
	 */

	public static String LABEL_REDUCEGRAPH			= "Don't reduce graph. Just shift assumptions into edges";
	public static String LABEL_MERGEPARALLELEDGES	= "Merge parallel edges when reducing";
	
	/*
	 * default values for the different preferences
	 */

	public static boolean VALUE_REDUCEGRAPH_DEFAULT 		= false;
	public static boolean VALUE_MERGEPARALLELEDGES_DEFAULT	= false;
	
	
	
}
