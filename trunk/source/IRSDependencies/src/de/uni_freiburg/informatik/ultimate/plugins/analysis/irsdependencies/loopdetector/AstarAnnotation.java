package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector;

import java.lang.reflect.Field;

import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;

class AstarAnnotation<EDGE> extends AbstractAnnotations implements Comparable<AstarAnnotation<EDGE>> {

	private static final long serialVersionUID = 1L;
	private EDGE mBackPointer;
	private int mCostSoFar; // g-value
	private int mExpectedCostToTarget; // f-value
	private int mLowestExpectedCost;

	AstarAnnotation() {
		setExpectedCostToTarget(Integer.MAX_VALUE);
		setLowestExpectedCost(Integer.MAX_VALUE);
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
	public int compareTo(AstarAnnotation<EDGE> o) {
		return 0;
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

	EDGE getBackPointer() {
		return mBackPointer;
	}

	void setBackPointer(EDGE backPointer) {
		mBackPointer = backPointer;
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
}