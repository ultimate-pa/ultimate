package de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain;

public class WeqSettings {
	public static final boolean FREEZE_ALL_IN_MANAGER = true;

//	static final boolean FLATTEN_WEQ_EDGES_BEFORE_JOIN = true;
	static final boolean FLATTEN_WEQ_EDGES_BEFORE_JOIN = false;

	static final boolean REPORT_EQ_DEQ_INPLACE = false;
	public static final boolean REMOVE_ELEMENT_INPLACE = false;
	public static final boolean ADD_NODE_INPLACE = false;
	public static final boolean PROJECTTOELEMENTS_INPLACE = false;

	/**
	 * the rules pi^#-roweq and pi^
	 */
	public static final boolean INTRODUCE_AT_MOST_ONE_NODE_FOR_EACH_REMOVED_NODE = false;

}