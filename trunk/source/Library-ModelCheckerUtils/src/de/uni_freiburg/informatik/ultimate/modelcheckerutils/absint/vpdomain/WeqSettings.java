package de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain;

public class WeqSettings {
//	public static final boolean FREEZE_ALL_IN_MANAGER = true;

//	static final boolean FLATTEN_WEQ_EDGES_BEFORE_JOIN = true;
	static final boolean FLATTEN_WEQ_EDGES_BEFORE_JOIN = false;

	static final boolean REPORT_EQ_DEQ_INPLACE = true;

	public static final boolean REMOVE_ELEMENT_INPLACE = false;
	public static final boolean ADD_NODE_INPLACE = false;
	public static final boolean PROJECTTOELEMENTS_INPLACE = false;

	public static final boolean USE_FULL_WEQCC_DURING_PROJECTAWAY = true;
 	public static final boolean USE_FULL_WEQCC_DURING_CLOSURE = true;

	/**
	 * if reportChangeToGpa should be called during every report(Dis)Equality
	 */
	public static final boolean ALWAYS_REPORT_CHANGE_TO_GPA = false;

	/**
	 * the rules pi^#-roweq and pi^
	 */
	public static final boolean INTRODUCE_AT_MOST_ONE_NODE_FOR_EACH_REMOVED_NODE = false;

	/**
	 *
	 */

	/*
	 * toString settings
	 */
	public static final int MAX_NO_ELEMENTS_FOR_VERBOSE_TO_STRING = 20;
	public static final int MAX_NO_EDGELABELDISJUNCTS_FOR_VERBOSE_TO_STRING = 3;
	public static final int MAX_NO_WEQ_EDGES_FOR_VERBOSE_TO_STRING = 4;


	/* flags to switch sanity checks on/off */

	public static final boolean SANITYCHECK_AFTER_ADD_NODE = false;

	// general flag to capture e.g. sanity checks that are done for intermediate steps of a methods and similar ones
	public static final boolean SANITYCHECK_FINE_GRAINED = false;

	/**
	 * if reportChangeInGpa should perform a meet and project of the label
	 */
	static final boolean MEET_WITH_GPA_ON_REPORTCHANGE = false;

	static final boolean MEET_WITH_GPA_ON_REPORT_WEQ = false;

	public static final boolean MEET_WITH_GPA_PROJECT_OR_SHIFT_LABEL = false;
}
