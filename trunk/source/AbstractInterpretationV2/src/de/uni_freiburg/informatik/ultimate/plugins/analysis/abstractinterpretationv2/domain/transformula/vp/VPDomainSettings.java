package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

/**
 * Keeps settings that are not full-blown Ultimate preferences (those are in VPDomainPreferences).
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class VPDomainSettings {

//	/**
//	 * settings that are ultimate preferences
//	 */
//	public final boolean mUseWeqInProject;
//	public final boolean mFlattenBeforeFatten;
//	public final boolean mDeactivateWeakEquivalences;
//	public final boolean mPreciseComparisonOperator;


	/*
	 * switch some smt solver soundness checks on or off
	 */
	private final boolean mCheckPostCorrectness = false;
	private final boolean mCheckTransitionAbstractCorrectness = false;

	private final boolean mAddNodesBeforeAnsweringQuery = true;

	/**
	 * Initializes the settings that have a full-blown Ultimate preference
	 *
	 * @param ups
	 */
	public VPDomainSettings() {
//		mUseWeqInProject = ups.getBoolean(VPDomainPreferences.LABEL_USE_WEQ_IN_PROJECT);
//		mFlattenBeforeFatten = ups.getBoolean(VPDomainPreferences.LABEL_FLATTEN_BEFORE_FATTEN);
//		mDeactivateWeakEquivalences = ups.getBoolean(VPDomainPreferences.LABEL_DEACTIVATE_WEAK_EQUIVALENCES);
//		mPreciseComparisonOperator = ups.getBoolean(VPDomainPreferences.LABEL_PRECISE_COMPARISON_OPERATOR);
	}

	public boolean isCheckPostCorrectness() {
		return mCheckPostCorrectness;
	}
	public boolean isCheckTransitionAbstractionCorrectness() {
		return mCheckTransitionAbstractCorrectness;
	}

	/**
	 * Whether, at answering a EqState.areEqual or EqState.areUnequal query, the corresponding nodes should be added.
	 * Otherwise false will be returned if one of the nodes is not present in the EqState.
	 *
	 * @return
	 */
	public boolean isAddNodesBeforeAnsweringQuery() {
		return mAddNodesBeforeAnsweringQuery;
	}


}
