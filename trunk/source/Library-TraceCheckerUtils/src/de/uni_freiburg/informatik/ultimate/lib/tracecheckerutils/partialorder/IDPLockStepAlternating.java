/*
 * Copyright (C) 2026 Matthias Zumkeller
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.ConstantDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.WrapperVisitor;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptAnnotation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptAnnotation.ISRLocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;

/**
 * A preference order that approximates a schedule in which the context alternates between the main process and the
 * interrupt-service-routines. After each statement of the main program, an ISR determined by an alternative preference
 * order is scheduled next. After an ISR was scheduled, the next statement of the main program is preferred. This order
 * can be combined with a number of alternative orders, namely: {@link BetterLockstepOrder}, {@link LoopLockstepOrder},
 * {@link RandomDfsOrder}, {@link ConstantDfsOrder}.
 *
 * The order determines whether the last step was part on an ISR or part of the main program by recording the first edge
 * through which the state was first reached using a wrapper DFS visitor. The order is only working if this visitor is
 * used. If the alternative order also requires a specific visitor, this visitor is automatically wrapped by the wrapper
 * visitor of this class.
 *
 * @param <L>
 *            Type of the edges
 * @param <S>
 *            Type of the states
 */
public class IDPLockStepAlternating<L extends IAction, S> implements IDfsOrder<L, S> {
	private final Map<Object, L> mEntryEdge = new HashMap<>();
	private final Function<S, Object> mNormalizer;
	private final Function<L, InterruptAnnotation> mLetterToInterruptAnno;

	private final IDfsOrder<L, S> mAlternativeOrder;

	private final Function<S, Comparator<L>> mDefaultComparator;

	private final ILogger mLogger;

	/**
	 * Construct an order without alternative preference order. Instead a default comparator employing the procedure id
	 * and hash code is instrumented.
	 *
	 * @param services
	 * @param normalizer
	 * @param letterToIA
	 */
	public IDPLockStepAlternating(final IUltimateServiceProvider services, final Function<S, Object> normalizer,
			final Function<L, InterruptAnnotation> letterToIA) {
		mNormalizer = normalizer;
		mLetterToInterruptAnno = letterToIA;
		mLogger = services.getLoggingService().getLogger(getClass());
		mAlternativeOrder = null;

		mDefaultComparator = (s -> Comparator.comparing(L::getPrecedingProcedure).thenComparingInt(Object::hashCode));
		// mLogger.setLevel(LogLevel.DEBUG);
	}

	/**
	 * Construct an order that is composed with an alternative order which chooses the preferred next ISR in case the
	 * alternating order is currently preferring the ISRs. Also the alternative order is used to resolve non-determinism
	 * in the case that no edge is preferred by the alternating order.
	 *
	 * @param services
	 * @param normalizer
	 * @param letterToIA
	 * @param alternativeOrder
	 */
	public IDPLockStepAlternating(final IUltimateServiceProvider services, final Function<S, Object> normalizer,
			final Function<L, InterruptAnnotation> letterToIA, final IDfsOrder<L, S> alternativeOrder) {
		mNormalizer = normalizer;
		mLetterToInterruptAnno = letterToIA;
		mLogger = services.getLoggingService().getLogger(getClass());
		mAlternativeOrder = alternativeOrder;
		mDefaultComparator = alternativeOrder::getOrder;
		// mLogger.setLevel(LogLevel.DEBUG);
	}

	@Override
	public Comparator<L> getOrder(final S state) {
		final Object key = normalize(state);
		final L entryEdge = mEntryEdge.get(key);

		final var lastIA = entryEdge != null ? getLetterAnnotation(entryEdge) : null;
		return new IDPAlternatingComparator<>(mLogger, lastIA, mDefaultComparator.apply(state), mLetterToInterruptAnno);
	}

	private Object normalize(final S state) {
		if (mNormalizer == null) {
			return state;
		}
		return mNormalizer.apply(state);
	}

	private InterruptAnnotation getLetterAnnotation(final L letter) {
		return mLetterToInterruptAnno.apply(letter);
	}

	@Override
	public boolean isPositional() {
		return true;
	}

	public <V extends IDfsVisitor<L, S>> WrapperVisitor<L, S, IDfsVisitor<L, S>> wrapVisitor(final V underlying) {
		final WrapperVisitor<L, S, IDfsVisitor<L, S>> visitor = new Visitor<>(underlying);
		return wrapAlternativeVisitor(visitor);
	}

	public WrapperVisitor<L, S, IDfsVisitor<L, S>>
			wrapAlternativeVisitor(final WrapperVisitor<L, S, IDfsVisitor<L, S>> underlying) {
		if (mAlternativeOrder == null) {
			return underlying;
		} else if (mAlternativeOrder instanceof final BetterLockstepOrder<L, S> betterLockstepOrder) {
			return betterLockstepOrder.wrapVisitor(underlying);
		}
		return underlying;
	}

	public static final class IDPAlternatingComparator<L extends IAction> implements Comparator<L> {
		private final InterruptAnnotation mLastIA;
		private final Comparator<L> mFallback;
		private final Function<L, InterruptAnnotation> mGetLetterIA;
		ILogger mLogger;

		public IDPAlternatingComparator(final ILogger logger, final InterruptAnnotation lastIA,
				final Comparator<L> fallback, final Function<L, InterruptAnnotation> getLetterIA) {
			mLogger = logger;

			mLastIA = lastIA;
			mFallback = fallback;
			mGetLetterIA = getLetterIA;
		}

		@Override
		public int compare(final L x, final L y) {
			mLogger.debug("Interrupt level of entry edge: " + mLastIA);
			final var xIA = mGetLetterIA.apply(x);
			final var yIA = mGetLetterIA.apply(y);
			final boolean xHasIA = xIA != null;
			final boolean yHasIA = yIA != null;
			Integer res = null;
			if (mLastIA == null) {
				// If state entry has no inter. annotation, prefer edges with annotation
				res = Boolean.compare(yHasIA, xHasIA);
			} else if (isEntryAnnotation(mLastIA)) {
				// If state entry was an entry annotation prefer inner edges of the same interrupt
				final var xIsISRsucc = isInnerAnnotation(xIA) && belongToSameInterrupt(xIA, mLastIA);
				final var yIsISRsucc = isInnerAnnotation(yIA) && belongToSameInterrupt(yIA, mLastIA);
				res = Boolean.compare(yIsISRsucc, xIsISRsucc);
			} else if (isEntryAnnotation(xIA) || isEntryAnnotation(yIA)) {
				// If state entry is an edge of an ISR that is not an entry and x/y is an entry edge of the same
				// interrupt, prefer edges that are not interrupt entries of the same ISR
				final var xIsISREntry = isEntryAnnotation(xIA) && belongToSameInterrupt(xIA, mLastIA);
				final var yIsISREntry = isEntryAnnotation(yIA) && belongToSameInterrupt(yIA, mLastIA);
				res = Boolean.compare(xIsISREntry, yIsISREntry);
			} else {
				// Prefer edge without interrupt annotation otherwise
				res = Boolean.compare(xHasIA, yHasIA);
			}
			if (res != 0) {
				if (res == -1) {
					mLogger.debug("Prefered interrupt edge: " + xIA + " over " + yIA);
				} else {
					mLogger.debug("Preferered interrupt edge: " + yIA + " over " + xIA);
				}
				return res;
			}
			mLogger.debug("No preference for edges: " + xIA + " and " + yIA);
			return mFallback.compare(x, y);
		}

		private static boolean belongToSameInterrupt(final InterruptAnnotation iA1, final InterruptAnnotation iA2) {
			return iA1.getIrq().getNum() <= iA2.getIrq().getNum();
		}

		private static boolean isEntryAnnotation(final InterruptAnnotation interruptAnnotation) {
			return interruptAnnotation != null && interruptAnnotation.getLocation() == ISRLocation.ENTRY;
		}

		private static boolean isInnerAnnotation(final InterruptAnnotation interruptAnnotation) {
			return interruptAnnotation != null && interruptAnnotation.getLocation() == ISRLocation.ISR;
		}

		@Override
		public int hashCode() {
			return Objects.hash(mFallback, mLastIA);
		}

		@Override
		public boolean equals(final Object obj) {
			return this == obj || (obj instanceof final IDPAlternatingComparator<?> other
					&& Objects.equals(mFallback, other.mFallback) && Objects.equals(mLastIA, other.mLastIA));
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
