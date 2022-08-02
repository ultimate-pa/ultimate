package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.Comparator;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.MonitorProduct;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMonitorStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;

public class PartialPreferenceOrderCombination<L, S1, S2,S> implements IPreferenceOrder<L,S1,S2>{
	IPartialPreferenceOrder<L, S1, S2> mPartOrd;
	IPreferenceOrder<L, S1, S2> mTotOrd;
	
	
	public PartialPreferenceOrderCombination(IPartialPreferenceOrder<L, S1, S2> partOrd, 
			IPreferenceOrder<L, S1, S2> totOrd) {
		mPartOrd = partOrd;
		mTotOrd = totOrd;
	}

	@Override
	public boolean isPositional() {
		return mPartOrd.isPositional() || mTotOrd.isPositional();
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider getMonitor() {
		//gibts hier eine bessere Lösung?
		try {
			return new MonitorProduct<L,S2,S2,S>(mPartOrd.getMonitor(), mTotOrd.getMonitor(), 
					(IMonitorStateFactory<S2, S2, S>) new IMonitorStateFactory.Default<S2,S2>());
		} catch (AutomataLibraryException e) {
			throw new RuntimeException(e);
		}
	}

	@Override
	public IPartialComparator getPartialOrder(S1 stateProgram, S2 stateMonitor) {
		// transform back to Comparator
		return new PartialPreferenceOrderCombinationComparator<L, S1, S2>(
				mPartOrd.getPartialOrder(stateProgram, stateMonitor), 
				mTotOrd.getPartialOrder(stateProgram, stateMonitor));
	}
	
	public static final class PartialPreferenceOrderCombinationComparator<L, S1, S2> implements IPartialComparator<L> {
		IPartialComparator<L> mPartComp;
		IPartialComparator<L> mTotComp;

		public PartialPreferenceOrderCombinationComparator(IPartialComparator<L> partOrd, IPartialComparator<L> totOrd) {
			mPartComp = partOrd;
			mTotComp = totOrd;
		}

		@Override
		public ComparisonResult compare(final L x, final L y) {
			ComparisonResult partResult = mPartComp.compare(x, y);
			if (partResult != ComparisonResult.INCOMPARABLE) {
				return partResult;
			} else {
				return mTotComp.compare(x, y);
			}
		}

		@Override
		public int hashCode() {
			return Objects.hash(mPartComp, mTotComp);
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final PartialPreferenceOrderCombinationComparator<L,S1,S2> other = 
					(PartialPreferenceOrderCombinationComparator<L,S1,S2>) obj;
			return Objects.equals(mPartComp, other.mPartComp) && Objects.equals(mTotComp, other.mTotComp);
		}
	}

	@Override
	public Comparator<L> getOrder(S1 stateProgram, S2 stateMonitor) {
		//transform from IPartialComparator<L> to Comparator<L>
		//return this.getPartialOrder(stateProgram, stateMonitor);
		return null;
	}
	
}
