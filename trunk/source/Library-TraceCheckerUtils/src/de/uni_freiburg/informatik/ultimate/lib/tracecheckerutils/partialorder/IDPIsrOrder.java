package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.WrapperVisitor;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.IDPMainOrder.IDPMainComparator;

public class IDPIsrOrder<L extends IAction, S> implements IDfsOrder<L, S> {

	private final Comparator<L> mDefaultComparator =
			Comparator.comparing(L::getPrecedingProcedure).thenComparingInt(Object::hashCode);
	private final Map<Object, L> mEntryEdge = new HashMap<>();
	private final Function<S, Object> mNormalizer;

	public IDPIsrOrder() {
		this(null);
	}

	public IDPIsrOrder(final Function<S, Object> normalizer) {
		mNormalizer = normalizer;
	}

	@Override
	public Comparator<L> getOrder(final S state) {
		final Object key = normalize(state);
		final L entryEdge = mEntryEdge.get(key);

		if (entryEdge == null) {
			// should only happen for the initial state
			return mDefaultComparator;
		}

		return new IDPMainComparator<>(mDefaultComparator);
	}

	@Override
	public boolean isPositional() {
		return true;
	}

	public <V extends IDfsVisitor<L, S>> WrapperVisitor<L, S, V> wrapVisitor(final V underlying) {
		return new Visitor<>(underlying);
	}

	private Object normalize(final S state) {
		if (mNormalizer == null) {
			return state;
		}
		return mNormalizer.apply(state);
	}

	public static final class IDPIsrComparator<L extends IAction> implements Comparator<L> {
		private static String MAIN_THREAD = "ULTIMATE.start";
		private final Comparator<L> mFallback;

		public IDPIsrComparator(final Comparator<L> fallback) {
			mFallback = fallback;
		}

		@Override
		public int compare(final L x, final L y) {
			final String xThread = x.getPrecedingProcedure();
			final var xMainThread = xThread.equals(MAIN_THREAD);
			final String yThread = y.getPrecedingProcedure();
			final var yMainThread = yThread.equals(MAIN_THREAD);
			if (xMainThread && !yMainThread) {
				return -1;
			}

			if (!xMainThread && yMainThread) {
				return 1;
			}
			return mFallback.compare(x, y);
		}

	}

	private final class Visitor<V extends IDfsVisitor<L, S>> extends WrapperVisitor<L, S, V> {
		private Visitor(final V underlying) {
			super(underlying);
		}

		@Override
		public boolean discoverTransition(final S source, final L letter, final S target) {
			mEntryEdge.putIfAbsent(normalize(target), letter);
			return super.discoverTransition(source, letter, target);
		}
	}
}
