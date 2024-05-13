package de.uni_freiburg.informatik.ultimate.core.lib.models.annotation;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/*
 * Annotation for states that represent a test goal
 */
public class VarAssignmentReuseAnnotation extends ModernAnnotations {

	private static final long serialVersionUID = 1L;
	private static final String KEY = VarAssignmentReuseAnnotation.class.getName();
	public boolean secondCheck = false;
	public boolean mNegatedVA = false;
	public boolean mCoveredTestGoal = false;
	private final Map<String, Object> mMap = new HashMap<>();
	public ArrayList<Pair<Term, Term>> mVarAssignmentPair = new ArrayList<Pair<Term, Term>>();

	public ArrayList<VarAssignmentReuseAnnotation> mVAsInVAPrefix = new ArrayList<VarAssignmentReuseAnnotation>();

	public VarAssignmentReuseAnnotation mVAofOppositeBranch;
	public String mPrecedingProcedure = "";
	public String mLocationOfPrecedingProcedure = "";
	public boolean mIsActiveTestGoal = true;
	public boolean mUseCurrentTestGoal = false; // use this test goal instead of a previous
	public HashSet<VarAssignmentReuseAnnotation> mUnsatWithVAs = new HashSet<>();
	public Integer checkCount = 1; // is either 1 or 2

	public VarAssignmentReuseAnnotation mDefaultVA = null;

	public boolean mLastChecked = false; // true after checksat, false if in a trace but no

	public Integer mVaOrder = -1;

	public VarAssignmentReuseAnnotation() {

	}

	@Override
	public Map<String, Object> getAnnotationsAsMap() {
		return mMap;
	}

	@Override
	public String toString() {
		return mMap.toString();
	}

	public static VarAssignmentReuseAnnotation getAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, KEY, a -> (VarAssignmentReuseAnnotation) a);
	}

	public void annotate(final IElement node) {
		node.getPayload().getAnnotations().put(KEY, this);

	}

	public void setOppositeAnno(final VarAssignmentReuseAnnotation vaOpppositeBranch) {
		mVAofOppositeBranch = vaOpppositeBranch;
	}

	/*
	 * Warning replaces the current VA
	 */
	public void setVa(final ArrayList<Pair<Term, Term>> varAssignmentPair, final int vaOrder,
			final ArrayList<VarAssignmentReuseAnnotation> VAsInPrefix) {
		mVarAssignmentPair = varAssignmentPair;
		mVaOrder = vaOrder;
		mVAsInVAPrefix = VAsInPrefix;
	}

	public void removeCheck() {
		mIsActiveTestGoal = false;
	}

	/*
	 * there exist only 2 VA's that need to know the default. The first and its opposite
	 */
	public VarAssignmentReuseAnnotation setDefaultVa(final VarAssignmentReuseAnnotation defaultVA) {
		if (mDefaultVA == null) {
			if (defaultVA != null) {
				mDefaultVA = defaultVA;
			} else {
				mDefaultVA = new VarAssignmentReuseAnnotation();
			}
		}
		return mDefaultVA;
	}

	public String getPrecedingProcedure() {

		return mPrecedingProcedure;

	}
}
