package de.uni_freiburg.informatik.ultimate.core.lib.models.annotation;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;

/*
 * Annotation for states that represent a test goal
 */
public class TestGoalAnnotation extends ModernAnnotations {
	private static final long serialVersionUID = 1L;
	private static final String KEY = TestGoalAnnotation.class.getName();
	private final Map<String, Object> mMap = new HashMap<>();
	public int mId;

	public TestGoalAnnotation(final int countTestGoals) {
		mId = countTestGoals;
	}

	@Override
	public Map<String, Object> getAnnotationsAsMap() {
		return mMap;
	}

	@Override
	public String toString() {
		return mMap.toString();
	}

	public void setId(final int id) {
		mId = id;
	}

	public static TestGoalAnnotation getAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, KEY, a -> (TestGoalAnnotation) a);
	}

	public void annotate(final IElement node) {
		node.getPayload().getAnnotations().put(KEY, this);

	}
}
