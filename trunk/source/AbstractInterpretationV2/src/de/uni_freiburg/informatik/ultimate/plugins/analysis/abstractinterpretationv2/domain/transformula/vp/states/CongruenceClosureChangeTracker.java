package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ICongruenceClosureElement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

class CongruenceClosureChangeTracker<ACTION,
			NODE extends ICongruenceClosureElement<NODE, FUNCTION>,
			FUNCTION>
		extends CongruenceClosure<NODE, FUNCTION> {

	private final HashSet<Doubleton<NODE>> mFreshElementEqualities = new HashSet<>();
	private final HashSet<Doubleton<NODE>> mFreshElementDisequalities = new HashSet<>();
	private final HashSet<Doubleton<FUNCTION>> mFreshFunctionEqualities = new HashSet<>();
	private final HashSet<Doubleton<FUNCTION>> mFreshFunctionDisequalities = new HashSet<>();
	private boolean mBecameInconsistent = false;

	public CongruenceClosureChangeTracker(final CongruenceClosure<NODE, FUNCTION> originalCc) {
		super(originalCc);
	}

	@Override
	public boolean reportFunctionEquality(final FUNCTION func1, final FUNCTION func2) {
		final boolean madeChange = super.reportFunctionEquality(func1, func2);
		if (madeChange) {
			mFreshFunctionEqualities.add(new Doubleton<FUNCTION>(func1, func2));
		}
		return madeChange;
	}

	@Override
	public boolean reportFunctionDisequality(final FUNCTION func1, final FUNCTION func2) {
		final boolean madeChange = super.reportFunctionDisequality(func1, func2);
		if (madeChange) {
			mFreshFunctionDisequalities.add(new Doubleton<FUNCTION>(func1, func2));
		}
		return madeChange;
	}

	@Override
	public boolean reportEquality(final NODE elem1, final NODE elem2) {
		final boolean madeChange = super.reportEquality(elem1, elem2);
		if (madeChange) {
			mFreshElementEqualities.add(new Doubleton<NODE>(elem1, elem2));
		}
		return madeChange;
	}

	@Override
	public boolean reportDisequality(final NODE elem1, final NODE elem2) {
		final boolean madeChange = super.reportDisequality(elem1, elem2);
		if (madeChange) {
			mFreshElementDisequalities.add(new Doubleton<NODE>(elem1, elem2));
		}
		return madeChange;
	}

	@Override
	protected boolean reportDisequalityRec(final NODE elem1, final NODE elem2,
			final NestedMap2<FUNCTION, NODE, Set<List<NODE>>> oldCcChild) {
		final boolean madeChange = super.reportDisequality(elem1, elem2);
		if (madeChange) {
			mFreshElementDisequalities.add(new Doubleton<NODE>(elem1, elem2));
		}
		return madeChange;
	}

	@Override
	protected boolean reportEqualityRec(final NODE elem1, final NODE elem2) {
		final boolean madeChange = super.reportEquality(elem1, elem2);
		if (madeChange) {
			mFreshElementEqualities.add(new Doubleton<NODE>(elem1, elem2));
		}
		return madeChange;
	}

	@Override
	protected void updateInconsistencyStatus() {
		super.updateInconsistencyStatus();
		mBecameInconsistent |= isInconsistent();
	}

	public HashSet<Doubleton<NODE>> getFreshElementEqualities() {
		return mFreshElementEqualities;
	}

	public HashSet<Doubleton<NODE>> getFreshElementDisequalities() {
		return mFreshElementDisequalities;
	}

	public HashSet<Doubleton<FUNCTION>> getFreshFunctionEqualities() {
		return mFreshFunctionEqualities;
	}

	public HashSet<Doubleton<FUNCTION>> getFreshFunctionDisequalities() {
		return mFreshFunctionDisequalities;
	}

	public boolean isBecameInconsistent() {
		return mBecameInconsistent;
	}


}