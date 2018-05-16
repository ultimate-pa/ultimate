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

	/**
	 * omit the finest grained class of sanity checks
	 */
	public static final boolean OMIT_SANITYCHECK_FINE_GRAINED_1 = true;
	/**
	 * omit the second-finest grained class of sanity checks
	 */
	public static final boolean OMIT_SANITYCHECK_FINE_GRAINED_2 = true;
	/**
	 * omit the third-finest grained class of sanity checks
	 */
	public static final boolean OMIT_SANITYCHECK_FINE_GRAINED_3 = false;

	/*
	 * settings related to caching in CcManager
	 */

	public static final boolean UNIFY_CCS = false;

	// if we want to use unification, we have to forbid in place computations (copy-on-write)
//	public static final boolean FORBID_INPLACE = UNIFY_CCS;
	public static final boolean FORBID_INPLACE = false;

	public static final boolean IMPLICIT_LITERAL_DISEQUALITIES = true;

	/**
	 * depends on the HeapSepSettings.ASSERT_FREEZE_VAR_LIT_DISEQUALITIES_INTO_SCRIPT
	 */
	public static final boolean ADD_NON_THEORYlITERAL_DISEQUALITIES_FOR_CHECKS = false;

}
