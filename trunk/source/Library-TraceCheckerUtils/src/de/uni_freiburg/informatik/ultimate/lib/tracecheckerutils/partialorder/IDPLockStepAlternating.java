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

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.WrapperVisitor;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptAnnotations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptAnnotations.ISRLocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;

public class IDPLockStepAlternating<L extends IAction, S> implements IDfsOrder<L, S> {
	private final Map<Object, L> mEntryEdge = new HashMap<>();
	private final Function<S, Object> mNormalizer;
	private final Function<L, InterruptAnnotations> mLetterToInterruptAnno;

	private final Comparator<L> mDefaultComparator =
			Comparator.comparing(L::getPrecedingProcedure).thenComparingInt(Object::hashCode);

	private final ILogger mLogger;

	public IDPLockStepAlternating(final IUltimateServiceProvider services, final Function<S, Object> normalizer,
			final Function<L, InterruptAnnotations> letterToIA) {
		mNormalizer = normalizer;
		mLetterToInterruptAnno = letterToIA;
		mLogger = services.getLoggingService().getLogger(getClass());
		// mLogger.setLevel(LogLevel.DEBUG);
	}

	@Override
	public Comparator<L> getOrder(final S state) {
		final Object key = normalize(state);
		final L entryEdge = mEntryEdge.get(key);

		final var lastIA = entryEdge != null ? getLetterAnnotation(entryEdge) : null;
		return new IDPAlternatingComparator<>(mLogger, lastIA, mDefaultComparator, mLetterToInterruptAnno);
	}

	private Object normalize(final S state) {
		if (mNormalizer == null) {
			return state;
		}
		return mNormalizer.apply(state);
	}

	private InterruptAnnotations getLetterAnnotation(final L letter) {
		return mLetterToInterruptAnno.apply(letter);
	}

	@Override
	public boolean isPositional() {
		return true;
	}

	public <V extends IDfsVisitor<L, S>> WrapperVisitor<L, S, V> wrapVisitor(final V underlying) {
		return new Visitor<>(underlying);
	}

	public static final class IDPAlternatingComparator<L extends IAction> implements Comparator<L> {
		private final InterruptAnnotations mLastIA;
		private final Comparator<L> mFallback;
		private final Function<L, InterruptAnnotations> mGetLetterIA;
		ILogger mLogger;

		public IDPAlternatingComparator(final ILogger logger, final InterruptAnnotations lastIA,
				final Comparator<L> fallback, final Function<L, InterruptAnnotations> getLetterIA) {
			mLastIA = lastIA;
			mFallback = fallback;
			mGetLetterIA = getLetterIA;
			mLogger = logger;
		}

		@Override
		public int compare(final L x, final L y) {
			mLogger.debug("Interrupt level of entry edge: " + mLastIA);
			final var xIA = mGetLetterIA.apply(x);
			final var yIA = mGetLetterIA.apply(y);
			final boolean xHasIA = xIA != null;
			final boolean yHasIA = yIA != null;
			assert !xHasIA || xIA.getIsrLocation() == ISRLocation.ENTRY;
			assert !yHasIA || yIA.getIsrLocation() == ISRLocation.ENTRY;
			Integer res = null;
			if (mLastIA == null) {
				res = Boolean.compare(yHasIA, xHasIA);
			} else if (isEntryAnnotation(mLastIA)) {
				final var xIsISRsucc = isInnerAnnotation(xIA) && belongToSameInterrupt(xIA, mLastIA);
				final var yIsISRsucc = isInnerAnnotation(yIA) && belongToSameInterrupt(yIA, mLastIA);
				res = Boolean.compare(yIsISRsucc, xIsISRsucc);
			} else if (isEntryAnnotation(xIA) || isEntryAnnotation(yIA)) {
				final var xIsISREntry = isEntryAnnotation(xIA) && belongToSameInterrupt(xIA, mLastIA);
				final var yIsISREntry = isEntryAnnotation(yIA) && belongToSameInterrupt(yIA, mLastIA);
				res = Boolean.compare(xIsISREntry, yIsISREntry);
			} else {
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

		private static boolean belongToSameInterrupt(final InterruptAnnotations iA1, final InterruptAnnotations iA2) {
			return iA1.getIsrId() == iA2.getIsrId();
		}

		private static boolean isEntryAnnotation(final InterruptAnnotations interruptAnnotation) {
			return interruptAnnotation != null && interruptAnnotation.getIsrLocation() == ISRLocation.ENTRY;
		}

		private static boolean isInnerAnnotation(final InterruptAnnotations interruptAnnotation) {
			return interruptAnnotation != null && interruptAnnotation.getIsrLocation() == ISRLocation.ISR;
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
