/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-srParse plug-in.
 *
 * The ULTIMATE Library-srParse plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-srParse plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-srParse plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-srParse plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-srParse plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * Immutable description of a single DC phase before it is materialized into a {@link DCPhase}.
 *
 * <p>
 * Unlike {@link DCPhase}, which stores the time bound as {@code int}, a {@link PhaseRecipe} stores it as
 * {@link Rational}. This allows the duration-normalization mechanism (scaling factor) to process countertrace bounds
 * the same way it processes regular pattern durations. After normalization, {@link #toDCPhase()} converts the
 * (now-integral) bound to {@code int} via {@link SmtUtils#toInt(Rational)}.
 * </p>
 *
 * @author University of Freiburg
 */
public final class PhaseRecipe {

	private final CDD mInvariant;
	private final int mBoundType;
	private final Rational mBound;
	private final boolean mAllowEmpty;

	private PhaseRecipe(final CDD invariant, final int boundType, final Rational bound, final boolean allowEmpty) {
		mInvariant = invariant;
		mBoundType = boundType;
		mBound = bound;
		mAllowEmpty = allowEmpty;
	}

	/**
	 * Factory for the {@code true} phase (unbounded, no invariant).
	 */
	public static PhaseRecipe truePhase() {
		return new PhaseRecipe(null, CounterTrace.BOUND_NONE, null, true);
	}

	/**
	 * Factory for an invariant-only phase {@code ⌈ expr ⌉} (unbounded).
	 */
	public static PhaseRecipe invariant(final CDD inv) {
		return new PhaseRecipe(inv, CounterTrace.BOUND_NONE, null, false);
	}

	/**
	 * Factory for a bounded phase {@code ⌈ expr ⌉ ∧ ℓ <op> n}.
	 *
	 * @param inv
	 *            invariant CDD
	 * @param boundType
	 *            one of {@link CounterTrace#BOUND_LESS}, {@link CounterTrace#BOUND_LESSEQUAL},
	 *            {@link CounterTrace#BOUND_GREATEREQUAL}, {@link CounterTrace#BOUND_GREATER}
	 * @param bound
	 *            time bound as {@link Rational} (will be scaled and converted to {@code int} later)
	 * @param allowEmpty
	 *            whether the phase may have zero duration (sub₀ variants)
	 */
	public static PhaseRecipe bounded(final CDD inv, final int boundType, final Rational bound,
			final boolean allowEmpty) {
		return new PhaseRecipe(inv, boundType, bound, allowEmpty);
	}

	/**
	 * @return the time bound as {@link Rational}, or {@code null} if this phase is unbounded.
	 */
	public Rational getBound() {
		return mBound;
	}

	/**
	 * Returns a new recipe whose bound is scaled by the given factor. If this phase is unbounded, returns {@code this}.
	 *
	 * @param scale
	 *            scaling factor (non-null)
	 * @return scaled recipe, or {@code this} if unbounded
	 */
	public PhaseRecipe scaleBound(final Rational scale) {
		if (mBound == null) {
			return this;
		}
		return new PhaseRecipe(mInvariant, mBoundType, mBound.mul(scale), mAllowEmpty);
	}

	/**
	 * Materializes this recipe into a {@link DCPhase}. The bound must be integral at this point (i.e. after
	 * normalization).
	 *
	 * @return a {@link DCPhase} corresponding to this recipe
	 * @throws IllegalStateException
	 *             if the bound is not integral
	 */
	public DCPhase toDCPhase() {
		if (mBound == null) {
			if (mInvariant == null) {
				return new DCPhase();
			}
			return new DCPhase(mInvariant);
		}
		final int intBound = SmtUtils.toInt(mBound).intValueExact();
		if (mAllowEmpty) {
			return new DCPhase(CDD.TRUE, mInvariant, mBoundType, intBound, java.util.Collections.emptySet(), true);
		}
		return new DCPhase(mInvariant, mBoundType, intBound);
	}

	@Override
	public int hashCode() {
		return Objects.hash(mInvariant, mBoundType, mBound, mAllowEmpty);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || getClass() != obj.getClass()) {
			return false;
		}
		final PhaseRecipe other = (PhaseRecipe) obj;
		return mBoundType == other.mBoundType && mAllowEmpty == other.mAllowEmpty
				&& Objects.equals(mInvariant, other.mInvariant) && Objects.equals(mBound, other.mBound);
	}
}
