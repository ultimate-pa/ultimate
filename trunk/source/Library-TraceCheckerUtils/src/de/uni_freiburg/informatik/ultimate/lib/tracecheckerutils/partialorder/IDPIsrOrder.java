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

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptAnnotations;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;

public class IDPIsrOrder<L extends IIcfgTransition<?>, S> implements IDfsOrder<L, S> {

	private final Comparator<L> mDefaultComparator =
			Comparator.comparing(L::getPrecedingProcedure).thenComparingInt(Object::hashCode);

	public IDPIsrOrder() {
	}

	@Override
	public Comparator<L> getOrder(final S state) {
		return new IDPIsrComparator<>(mDefaultComparator);
	}

	@Override
	public boolean isPositional() {
		return true;
	}

	public static final class IDPIsrComparator<L extends IIcfgTransition<?>> implements Comparator<L> {
		private final Comparator<L> mFallback;

		public IDPIsrComparator(final Comparator<L> fallback) {
			mFallback = fallback;
		}

		@Override
		public int compare(final L x, final L y) {
			final var xBelongsToIsr = InterruptAnnotations.hasAnnotation(x);
			final var yBelongsToIsr = InterruptAnnotations.hasAnnotation(y);

			if (xBelongsToIsr && !yBelongsToIsr) {
				return 1;
			} else if (!xBelongsToIsr && yBelongsToIsr) {
				return -1;
			}
			return mFallback.compare(x, y);
		}

	}
}
