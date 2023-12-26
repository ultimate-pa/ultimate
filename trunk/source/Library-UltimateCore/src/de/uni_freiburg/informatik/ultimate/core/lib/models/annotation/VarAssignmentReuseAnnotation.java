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
	private final Map<String, Object> mMap = new HashMap<>();
	public ArrayList<Pair<Term, Term>> mVarAssignmentPair = new ArrayList<Pair<Term, Term>>(); // check if negated,
																								// order corresponds to
																								// test-case
	public VarAssignmentReuseAnnotation mVAofOppositeBranch;
	public boolean mIsNegated = false;
	public boolean mIsActiveTestGoal = true;
	public boolean mUseCurrentTestGoal = false; // use this test goal instead of a previous
	public HashSet<VarAssignmentReuseAnnotation> mUnsatWithVAs = new HashSet<>();
	public Integer checkCount = 1; // is either 1 or 2

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
	public void setVa(final ArrayList<Pair<Term, Term>> varAssignmentPair) {
		mVarAssignmentPair = varAssignmentPair;
	}

	// Do not negate here, only flag as negated. Negate the formula when asserting the term
	public void negateVa() {
		mIsNegated = true;
	}

	public void removeCheck() {
		mIsActiveTestGoal = false;
	}
}
