package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

class EqClassSegmentation {
	private final List<Set<Term>> mBounds;
	private final List<IProgramVar> mFirstValues;
	private final List<IProgramVar> mSecondValues;

	public EqClassSegmentation(final List<Set<Term>> bounds, final List<IProgramVar> firstValues,
			final List<IProgramVar> secondValues) {
		mBounds = bounds;
		mFirstValues = firstValues;
		mSecondValues = secondValues;
	}

	public List<Set<Term>> getBounds() {
		return mBounds;
	}

	public List<IProgramVar> getFirstValues() {
		return mFirstValues;
	}

	public List<IProgramVar> getSecondValues() {
		return mSecondValues;
	}

	@Override
	public String toString() {
		final StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append("{-inf} ").append(mFirstValues.get(0)).append(" / ").append(mSecondValues.get(0));
		for (int i = 0; i < mFirstValues.size() - 1; i++) {
			stringBuilder.append(' ').append(mBounds.get(i).toString().replace('[', '{').replace(']', '}'));
			stringBuilder.append(' ').append(mFirstValues.get(i + 1)).append(" / ").append(mSecondValues.get(i + 1));
		}
		return stringBuilder.append(" {inf}").toString();
	}
}
