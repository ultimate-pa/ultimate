package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector;

import java.lang.reflect.Field;

import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 * @param <E>
 */
class AstarAnnotation<E> extends AbstractAnnotations implements Comparable<AstarAnnotation<E>> {

	private static final long serialVersionUID = 1L;
	private static int sId;
	private final int mId;

	private E mPreEdge;
	private int mCostSoFar; // g-value
	private int mExpectedCostToTarget; // f-value
	private int mLowestExpectedCost; // h-value

	AstarAnnotation() {
		setExpectedCostToTarget(Integer.MAX_VALUE);
		setLowestExpectedCost(Integer.MAX_VALUE);
		mId = sId++;
	}

	void setExpectedCostToTarget(int value) {
		mExpectedCostToTarget = value;
		if (value < getLowestExpectedCost()) {
			setLowestExpectedCost(value);
		}
	}

	boolean isLowest() {
		return getLowestExpectedCost() == getExpectedCostToTarget();
	}

	@Override
	public int compareTo(AstarAnnotation<E> o) {
		return Integer.compare(mExpectedCostToTarget, o.mExpectedCostToTarget);
	}

	@Override
	protected String[] getFieldNames() {
		return new String[] { "mBackPointer", "mCostSoFar", "mExpectedCostToTarget" };
	}

	@Override
	protected Object getFieldValue(String field) {
		try {
			Field f = getClass().getDeclaredField(field);
			f.setAccessible(true);
			return f.get(this);
		} catch (Exception ex) {
			return ex;
		}
	}

	E getPreEdge() {
		return mPreEdge;
	}

	void setBackPointers(E backEdge) {
		mPreEdge = backEdge;
	}

	int getCostSoFar() {
		return mCostSoFar;
	}

	void setCostSoFar(int costSoFar) {
		mCostSoFar = costSoFar;
	}

	int getExpectedCostToTarget() {
		return mExpectedCostToTarget;
	}

	private int getLowestExpectedCost() {
		return mLowestExpectedCost;
	}

	private void setLowestExpectedCost(int lowestExpectedCost) {
		mLowestExpectedCost = lowestExpectedCost;
	}

	@Override
	public int hashCode() {
		return mId;
	}
}