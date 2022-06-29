package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.Comparator;
import java.util.HashSet;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.ParameterizedOrderAutomaton.State;

public class ParameterizedOrder<L extends IIcfgTransition<?>, S2> implements IPreferenceOrder<L, State, S2>{
	private final Set<String> mThreads = new HashSet<>();
	private static Integer mParameter;
	private Set<L> mAlphabet;
	private INwaOutgoingLetterAndTransitionProvider<L, State> mMonitor;
	private final Comparator<L> mDefaultComparator =
			Comparator.comparing(L::getPrecedingProcedure).thenComparingInt(Object::hashCode);

	public ParameterizedOrder(Integer parameter) {
		mParameter = parameter;
		mMonitor = new ParameterizedOrderAutomaton(mParameter, mThreads, null); //hier muss dann isStep übergeben werden
	}
	
	@Override
	public Comparator<L> getOrder(State stateParameterized, S2 stateProgram) {
		// TODO vom Prinzip genau wie der RoundRobinComparator
		final String lastThread = ((de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.ParameterizedOrderAutomaton.State) stateParameterized).getThread();
		final Integer lastCounter = ((de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.ParameterizedOrderAutomaton.State) stateParameterized).getCounter();
		return new ParameterizedComparator<>(lastThread, mDefaultComparator, lastCounter);
	}
	
	public static final class ParameterizedComparator<L extends IAction> implements Comparator<L> {
		private final String mLastThread;
		private final Comparator<L> mFallback;
		private final Integer mLastCounter;

		public ParameterizedComparator(final String lastThread, final Comparator<L> fallback, final Integer lastCounter) {
			mLastThread = Objects.requireNonNull(lastThread);
			mFallback = fallback;
			mLastCounter = lastCounter;
		}

		@Override
		public int compare(final L x, final L y) {
			final String xThread = x.getPrecedingProcedure();
			final boolean xBefore = mLastThread.compareTo(xThread) > 0;
			final boolean xEqual = mLastThread.compareTo(xThread) == 0;
			final String yThread = y.getPrecedingProcedure();
			final boolean yBefore = mLastThread.compareTo(yThread) > 0;
			final boolean yEqual = mLastThread.compareTo(yThread) == 0;
			
			if (xEqual && mLastCounter < mParameter) {
				return 1;
			}
			if (yEqual && mLastCounter < mParameter) {
				return -1;
			}
			if (xBefore && !yBefore) {
				return 1;
			}
			if (yBefore && !xBefore) {
				return -1;
			}
			return mFallback.compare(x, y); //also captures the case were xEqual or yEqual, but mLastCOunter reached mParameter
		}

		@Override
		public int hashCode() {
			return Objects.hash(mFallback, mLastThread);
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
			final ParameterizedComparator<L> other = (ParameterizedComparator<L>) obj;
			return Objects.equals(mFallback, other.mFallback) && Objects.equals(mLastThread, other.mLastThread);
		}
	}

	@Override
	public boolean isPositional() {
		return true;
	}
	
	@Override
	public INwaOutgoingLetterAndTransitionProvider<L, State> getMonitor() {
		return mMonitor;
	}

}
