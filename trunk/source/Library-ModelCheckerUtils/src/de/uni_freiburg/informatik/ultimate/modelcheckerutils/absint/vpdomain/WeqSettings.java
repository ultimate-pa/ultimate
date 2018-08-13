package de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain;

public class WeqSettings {
//	public final boolean FREEZE_ALL_IN_MANAGER = true;

//	final boolean FLATTEN_WEQ_EDGES_BEFORE_JOIN = true;
	// TOOD: is this a good name? was it "before join", not before meetWGpa/fattenWeq/project??
	private boolean mFlattenWeqEdgesBeforeWeqFatten = false;

	private final boolean mReportEqDeqInplace = true;


	private final boolean mRemoveElementInplace = false;
	private final boolean mAddNodeInplace = false;
	private final boolean mProjectToElementsInplace = false;



	private boolean mUseFullWeqccDuringProjectAway = true;

	private boolean mDeactivateWeakEquivalences = false;

	// setting would not work -- weq-prime architecture would need rework
// 	private final boolean USE_FULL_WEQCC_DURING_CLOSURE = true;

	/**
	 * if reportChangeToGpa should be called during every report(Dis)Equality
	 */
	private final boolean mAlwaysReportChangeToGpa = false;

	/**
	 * the rules pi^#-roweq and pi^
	 */
	private final boolean mIntroduceAtMostOneNodeForEachRemovedNode = false;

	/*
	 * toString settings
	 */
	private final int mMaxNoElementsForVerboseToString = 20;
	private final int mMaxNoEdgeLabelDisjunctsForVerboseToString = 3;
	private final int mMaxNoWeqEdgesForVerboseToString = 4;


	/* flags to switch sanity checks on/off */

//	private final boolean SANITYCHECK_AFTER_ADD_NODE = false;

	// general flag to capture e.g. sanity checks that are done for intermediate steps of a methods and similar ones

	// very fine grained checks
	private final boolean mOmitSanityCheckFineGrained1 = true;

	// still fine grained checks but less
	private final boolean mOmitSanityCheckFineGrained2 = true;

	/**
	 * if reportChangeInGpa should perform a meet and project of the label
	 */
	private final boolean mMeetWithGpaOnReportChange = false;

	private final boolean mMeetWithGpaOnReportWeq = false;

	/**
	 * TODO Should we always do meetWGpa during the label operations done in the roweq-rules?? Does it commute???
	 * (observation, 02.01.2018: does seem to impact precision on regression tests, negatively if false)
	 */
	private final boolean mMeetWithGpaProjectOrShiftLabel = true;

	/**
	 * if weq labels are compared via an SMT query (right now: the standard solver, probably doing it via SMTInterpol
	 * would be better) or via our imprecise disjunct-by-disjunct check
	 * (performance on regressions: slightly worse for "true", ~5-10%)
	 */
	private boolean mPreciseWeqLabelComparison = false;

	/**
	 * Whether before answering an equality query (in EqConstraint and the like, not the low-level ones like
	 * getEqualityStatus) the nodes should be added
	 */
	private final boolean mAddNodesBeforeAnsweringQuery = true;

	public WeqSettings() {

	}

	public boolean isFlattenWeqEdgesBeforeMeetWWeqGpa() {
		return mFlattenWeqEdgesBeforeWeqFatten;
	}

	public boolean isReportEqDeqInplace() {
		return mReportEqDeqInplace;
	}

	public boolean isRemoveElementInplace() {
		return mRemoveElementInplace;
	}

	public boolean isAddNodeInplace() {
		return mAddNodeInplace;
	}

	public boolean isProjecttoelementsInplace() {
		return mProjectToElementsInplace;
	}

	public boolean isUseFullWeqccDuringProjectaway() {
		return mUseFullWeqccDuringProjectAway;
	}

	public boolean isAlwaysReportChangeToGpa() {
		return mAlwaysReportChangeToGpa;
	}

	public boolean isIntroduceAtMostOneNodeForEachRemovedNode() {
		return mIntroduceAtMostOneNodeForEachRemovedNode;
	}

	public int getMaxNoElementsForVerboseToString() {
		return mMaxNoElementsForVerboseToString;
	}

	public int getMaxNoEdgelabeldisjunctsForVerboseToString() {
		return mMaxNoEdgeLabelDisjunctsForVerboseToString;
	}

	public int getMaxNoWeqEdgesForVerboseToString() {
		return mMaxNoWeqEdgesForVerboseToString;
	}

	public boolean omitSanitycheckFineGrained1() {
		return mOmitSanityCheckFineGrained1;
	}

	public boolean omitSanitycheckFineGrained2() {
		return mOmitSanityCheckFineGrained2;
	}

	public boolean isMeetWithGpaOnReportchange() {
		return mMeetWithGpaOnReportChange;
	}

	public boolean isMeetWithGpaOnReportWeq() {
		return mMeetWithGpaOnReportWeq;
	}

	public boolean isMeetWithGpaProjectOrShiftLabel() {
		return mMeetWithGpaProjectOrShiftLabel;
	}

	public boolean isPreciseWeqLabelComparison() {
		return mPreciseWeqLabelComparison;
	}

	public boolean isDeactivateWeakEquivalences() {
		return mDeactivateWeakEquivalences;
	}

	public void setUseFullWeqccDuringProjectaway(final boolean b) {
		mUseFullWeqccDuringProjectAway = b;
	}

	public void setDeactivateWeakEquivalences(final boolean b) {
		mDeactivateWeakEquivalences = b;
	}

	public void setFlattenWeqEdgesBeforeMeetWWeqGpa(final boolean b) {
		mFlattenWeqEdgesBeforeWeqFatten = b;
	}

	public void setPreciseWeqLabelComparison(final boolean b) {
		mPreciseWeqLabelComparison = b;
	}

	public boolean isAddNodesBeforeAnsweringQuery() {
		return mAddNodesBeforeAnsweringQuery;
	}

	/**
	 * WeqCcs in EqConstraints need to be frozen, but they do not always need to be closed. If this returns true, then
	 * all WeqCcs that are kept in EqConstraint are always also closed.
	 * (Historically, a freeze meant a close, by this setting, these concerns are separated.)
	 *
	 * @return
	 */
	public boolean closeAllEqConstraints() {
		return !true;
	}
}
