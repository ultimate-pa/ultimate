package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public class UnificationResult<STATE extends IAbstractState<STATE>> {
	private final STATE mFirstSubstate;
	private final STATE mSecondSubstate;
	private final List<Set<Term>> mBounds;
	private final List<IProgramVar> mFirstValues;
	private final List<IProgramVar> mSecondValues;

	public UnificationResult(final STATE firstSubstate, final STATE secondSubstate, final List<Set<Term>> bounds,
			final List<IProgramVar> firstValues, final List<IProgramVar> secondValues) {
		mFirstSubstate = firstSubstate;
		mSecondSubstate = secondSubstate;
		mBounds = bounds;
		mFirstValues = firstValues;
		mSecondValues = secondValues;
	}

	public STATE getFirstSubstate() {
		return mFirstSubstate;
	}

	public STATE getSecondSubstate() {
		return mSecondSubstate;
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
}
