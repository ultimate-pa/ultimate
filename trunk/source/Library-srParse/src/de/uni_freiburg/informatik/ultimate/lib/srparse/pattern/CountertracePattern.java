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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase;
import de.uni_freiburg.informatik.ultimate.lib.srparse.Durations;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlobally;
import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * A {@link PatternType} backed by a list of {@link PhaseRecipe}s parsed from countertrace notation in a {@code .req}
 * file.
 *
 * <p>
 * Unlike regular srParse patterns (e.g., {@code AbsencePattern}) which construct their {@link CounterTrace}
 * programmatically from CDDs and durations in {@link #transform(CDD[], int[])}, a {@link CountertracePattern} stores
 * phase recipes with {@link Rational} time bounds. This allows the bounds to participate in the duration-normalization
 * mechanism (scaling factor) just like regular pattern durations. The {@link CounterTrace} is only materialized in
 * {@link #constructCounterTrace()}, after normalization has scaled all bounds to integers.
 * </p>
 *
 * @author University of Freiburg
 */
public class CountertracePattern extends PatternType<CountertracePattern> {

	private static final SrParseScopeGlobally GLOBALLY_SCOPE = new SrParseScopeGlobally();

	private final List<PhaseRecipe> mRecipes;

	public CountertracePattern(final String id, final List<PhaseRecipe> recipes) {
		this(GLOBALLY_SCOPE, id, recipes);
	}

	public CountertracePattern(final SrParseScope<?> scope, final String id, final List<PhaseRecipe> recipes) {
		super(scope, id, Collections.emptyList(), Collections.emptyList(), Collections.emptyList());
		mRecipes = List.copyOf(Objects.requireNonNull(recipes));
	}

	/**
	 * Returns the time bounds of all bounded phases as {@link Rational}s. This allows
	 * {@link Durations#addNonInitPattern(PatternType)} to include countertrace bounds in the scaling-factor
	 * computation.
	 *
	 * @return unmodifiable list of non-null bounds
	 */
	@Override
	public List<Rational> getDurations() {
		return mRecipes.stream().map(PhaseRecipe::getBound).filter(Objects::nonNull).collect(Collectors.toList());
	}

	/**
	 * Materializes the {@link CounterTrace} from the (normalized) recipes. Overrides
	 * {@link PatternType#constructCounterTrace()} to bypass {@code getDurationsAsIntArray()} and build {@link DCPhase}s
	 * directly from the recipes.
	 */
	@Override
	public List<CounterTrace> constructCounterTrace() {
		final DCPhase[] phases = new DCPhase[mRecipes.size()];
		for (int i = 0; i < mRecipes.size(); i++) {
			phases[i] = mRecipes.get(i).toDCPhase();
		}
		return Collections.singletonList(new CounterTrace(phases));
	}

	@Override
	protected List<CounterTrace> transform(final CDD[] cdds, final int[] durations) {
		return constructCounterTrace();
	}

	/**
	 * Scales all recipe bounds by the scaling factor computed from {@link Durations}. Returns {@code this} if the
	 * scaling factor is {@code 1}.
	 */
	public CountertracePattern normalize(final Durations durations) {
		final Rational scale = durations.computeScalingFactor();
		if (scale.equals(Rational.ONE)) {
			return this;
		}
		final List<PhaseRecipe> scaled =
				mRecipes.stream().map(r -> r.scaleBound(scale)).collect(Collectors.toList());
		return new CountertracePattern(getScope(), getId(), scaled);
	}

	@Override
	public CountertracePattern create(final SrParseScope<?> scope, final String id, final List<CDD> cdds,
			final List<Rational> durations, final List<String> durationNames) {
		return new CountertracePattern(scope, id, mRecipes);
	}

	@Override
	public CountertracePattern rename(final String newName) {
		return new CountertracePattern(getScope(), newName, mRecipes);
	}

	@Override
	public int getExpectedCddSize() {
		return 0;
	}

	@Override
	public int getExpectedDurationSize() {
		return 0;
	}

	@Override
	public String toString() {
		return getId() + ": " + constructCounterTrace().get(0).toString();
	}

	/**
	 * Convenience method that materializes and returns the single {@link CounterTrace}.
	 */
	public CounterTrace getCounterTrace() {
		return constructCounterTrace().get(0);
	}

	@Override
	public int hashCode() {
		return Objects.hash(super.hashCode(), mRecipes);
	}

	@Override
	public boolean equals(final Object obj) {
		if (!super.equals(obj)) {
			return false;
		}
		final CountertracePattern other = (CountertracePattern) obj;
		return Objects.equals(mRecipes, other.mRecipes);
	}
}
