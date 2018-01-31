package de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain;

public class WeqSettings {
//	public final boolean FREEZE_ALL_IN_MANAGER = true;

//	final boolean FLATTEN_WEQ_EDGES_BEFORE_JOIN = true;
	// TOOD: is this a good name? was it "before join", not before meetWGpa/fattenWeq/project??
	private boolean FLATTEN_WEQ_EDGES_BEFORE_WEQ_FATTEN = false;

	private final boolean REPORT_EQ_DEQ_INPLACE = true;


	private final boolean REMOVE_ELEMENT_INPLACE = false;
	private final boolean ADD_NODE_INPLACE = false;
	private final boolean PROJECTTOELEMENTS_INPLACE = false;



	private boolean USE_FULL_WEQCC_DURING_PROJECTAWAY = true;

	private boolean DEACTIVATE_WEAK_EQUIVALENCES = false;

	// setting would not work -- weq-prime architecture would need rework
// 	private final boolean USE_FULL_WEQCC_DURING_CLOSURE = true;

	/**
	 * if reportChangeToGpa should be called during every report(Dis)Equality
	 */
	private final boolean ALWAYS_REPORT_CHANGE_TO_GPA = false;

	/**
	 * the rules pi^#-roweq and pi^
	 */
	private final boolean INTRODUCE_AT_MOST_ONE_NODE_FOR_EACH_REMOVED_NODE = false;

	/*
	 * toString settings
	 */
	private final int MAX_NO_ELEMENTS_FOR_VERBOSE_TO_STRING = 20;
	private final int MAX_NO_EDGELABELDISJUNCTS_FOR_VERBOSE_TO_STRING = 3;
	private final int MAX_NO_WEQ_EDGES_FOR_VERBOSE_TO_STRING = 4;


	/* flags to switch sanity checks on/off */

//	private final boolean SANITYCHECK_AFTER_ADD_NODE = false;

	// general flag to capture e.g. sanity checks that are done for intermediate steps of a methods and similar ones

	// very fine grained checks
	private final boolean OMIT_SANITYCHECK_FINE_GRAINED_1 = true;

	// still fine grained checks but less
	private final boolean OMIT_SANITYCHECK_FINE_GRAINED_2 = true;

	/**
	 * if reportChangeInGpa should perform a meet and project of the label
	 */
	private final boolean MEET_WITH_GPA_ON_REPORTCHANGE = false;

	private final boolean MEET_WITH_GPA_ON_REPORT_WEQ = false;

	/**
	 * TODO Should we always do meetWGpa during the label operations done in the roweq-rules?? Does it commute???
	 * (observation, 02.01.2018: does seem to impact precision on regression tests, negatively if false)
	 */
	private final boolean MEET_WITH_GPA_PROJECT_OR_SHIFT_LABEL = true;

	/**
	 * if weq labels are compared via an SMT query (right now: the standard solver, probably doing it via SMTInterpol
	 * would be better) or via our imprecise disjunct-by-disjunct check
	 * (performance on regressions: slightly worse for "true", ~5-10%)
	 */
	private boolean PRECISE_WEQ_LABEL_COMPARISON = false;

	public WeqSettings() {

	}

	public boolean isFlattenWeqEdgesBeforeMeetWWeqGpa() {
		return FLATTEN_WEQ_EDGES_BEFORE_WEQ_FATTEN;
	}

	public boolean isReportEqDeqInplace() {
		return REPORT_EQ_DEQ_INPLACE;
	}

	public boolean isRemoveElementInplace() {
		return REMOVE_ELEMENT_INPLACE;
	}

	public boolean isAddNodeInplace() {
		return ADD_NODE_INPLACE;
	}

	public boolean isProjecttoelementsInplace() {
		return PROJECTTOELEMENTS_INPLACE;
	}

	public boolean isUseFullWeqccDuringProjectaway() {
		return USE_FULL_WEQCC_DURING_PROJECTAWAY;
	}

	public boolean isAlwaysReportChangeToGpa() {
		return ALWAYS_REPORT_CHANGE_TO_GPA;
	}

	public boolean isIntroduceAtMostOneNodeForEachRemovedNode() {
		return INTRODUCE_AT_MOST_ONE_NODE_FOR_EACH_REMOVED_NODE;
	}

	public int getMaxNoElementsForVerboseToString() {
		return MAX_NO_ELEMENTS_FOR_VERBOSE_TO_STRING;
	}

	public int getMaxNoEdgelabeldisjunctsForVerboseToString() {
		return MAX_NO_EDGELABELDISJUNCTS_FOR_VERBOSE_TO_STRING;
	}

	public int getMaxNoWeqEdgesForVerboseToString() {
		return MAX_NO_WEQ_EDGES_FOR_VERBOSE_TO_STRING;
	}

	public boolean omitSanitycheckFineGrained1() {
		return OMIT_SANITYCHECK_FINE_GRAINED_1;
	}

	public boolean omitSanitycheckFineGrained2() {
		return OMIT_SANITYCHECK_FINE_GRAINED_2;
	}

	public boolean isMeetWithGpaOnReportchange() {
		return MEET_WITH_GPA_ON_REPORTCHANGE;
	}

	public boolean isMeetWithGpaOnReportWeq() {
		return MEET_WITH_GPA_ON_REPORT_WEQ;
	}

	public boolean isMeetWithGpaProjectOrShiftLabel() {
		return MEET_WITH_GPA_PROJECT_OR_SHIFT_LABEL;
	}

	public boolean isPreciseWeqLabelComparison() {
		return PRECISE_WEQ_LABEL_COMPARISON;
	}

	public boolean isDeactivateWeakEquivalences() {
		return DEACTIVATE_WEAK_EQUIVALENCES;
	}

	public void setUseFullWeqccDuringProjectaway(final boolean b) {
		USE_FULL_WEQCC_DURING_PROJECTAWAY = b;
	}

	public void setDeactivateWeakEquivalences(final boolean b) {
		DEACTIVATE_WEAK_EQUIVALENCES = b;
	}

	public void setFlattenWeqEdgesBeforeMeetWWeqGpa(final boolean b) {
		FLATTEN_WEQ_EDGES_BEFORE_WEQ_FATTEN = b;
	}

	public void setPreciseWeqLabelComparison(final boolean b) {
		PRECISE_WEQ_LABEL_COMPARISON = b;
	}
}
