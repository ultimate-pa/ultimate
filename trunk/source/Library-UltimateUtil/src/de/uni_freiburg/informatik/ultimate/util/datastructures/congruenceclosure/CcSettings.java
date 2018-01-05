package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

public class CcSettings {
	static final boolean MEET_WITH_WEQ_CC = true;

//	public static final boolean FREEZE_ALL_IN_MANAGER = true;

	public static final boolean REPORT_EQ_DEQ_INPLACE = false;
	public static final boolean REMOVE_ELEMENT_INPLACE = false;
	public static final boolean ADD_NODE_INPLACE = false;
	public static final boolean PROJECTTOELEMENTS_INPLACE = false;

	public static final int MAX_NO_ELEMENTS_FOR_VERBOSE_TO_STRING = 20;

	public static final boolean DELAY_EXT_AND_DELTA_CLOSURE = true;

	public static final boolean SANITYCHECK_FINE_GRAINED = false;

	/*
	 * settings related to caching in CcManager
	 */

	public static final boolean UNIFY_CCS = false;

	// if we want to use unification, we have to forbid in place computations (copy-on-write)
	public static final boolean FORBID_INPLACE = UNIFY_CCS;

}
