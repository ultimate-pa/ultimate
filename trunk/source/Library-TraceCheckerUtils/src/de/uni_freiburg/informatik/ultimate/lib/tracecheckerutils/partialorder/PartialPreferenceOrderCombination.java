package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.Comparator;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.MonitorProduct;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMonitorStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator.ComparisonResult;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class PartialPreferenceOrderCombination<L, S1, S2,S3> implements IPreferenceOrder<L,S1,Pair<S2,S3>>{
	IPartialPreferenceOrder<L, S1, S2> mPartOrd;
	IPreferenceOrder<L, S1, S3> mTotOrd;
	
	
	public PartialPreferenceOrderCombination(IPartialPreferenceOrder<L, S1, S2> partOrd, 
			IPreferenceOrder<L, S1, S3> totOrd) {
		mPartOrd = partOrd;
		mTotOrd = totOrd;
	}

	@Override
	public boolean isPositional() {
		return mPartOrd.isPositional() || mTotOrd.isPositional();
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<L,Pair<S2,S3>> getMonitor() {
		try {
			return new MonitorProduct<L,S2,S3,Pair<S2,S3>>(mPartOrd.getMonitor(), mTotOrd.getMonitor(), 
					new IMonitorStateFactory.Default<S2,S3>());
		} catch (AutomataLibraryException e) {
			throw new RuntimeException(e);
		}
	}

	
	public static final class PartialPreferenceOrderCombinationComparator<L, S1, S2> implements Comparator<L> {
		IPartialComparator<L> mPartComp;
		Comparator<L> mTotComp;

		public PartialPreferenceOrderCombinationComparator(IPartialComparator<L> partOrd, Comparator<L> totOrd) {
			mPartComp = partOrd;
			mTotComp = totOrd;
		}

		@Override
		public int compare(final L x, final L y) {
			ComparisonResult partResult = mPartComp.compare(x, y);
			if (partResult == ComparisonResult.EQUAL) {
				return 0;
			} else if(partResult == ComparisonResult.STRICTLY_GREATER){
				return 1;
			} else if(partResult == ComparisonResult.STRICTLY_SMALLER) {
				return -1;
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
	public Comparator<L> getOrder(S1 stateProgram, Pair<S2,S3> stateMonitor) {
		return new PartialPreferenceOrderCombinationComparator<L, S1, S2>(
				mPartOrd.getPartialOrder(stateProgram, stateMonitor.getFirst()), 
				mTotOrd.getOrder(stateProgram, stateMonitor.getSecond()));
	}
	
}
