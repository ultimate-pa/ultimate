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

import java.util.Collections;
import java.util.List;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlobally;
import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * A {@link PatternType} that wraps a pre-built {@link CounterTrace} from countertrace notation in a {@code .req} file.
 *
 * <p>
 * Unlike regular srParse patterns (e.g., {@code AbsencePattern}) which construct their {@link CounterTrace}
 * programmatically from CDDs and durations in {@link #transform(CDD[], int[])}, a {@link CountertracePattern} already
 * has the fully parsed {@link CounterTrace} available. {@link #transform(CDD[], int[])} simply returns it.
 * </p>
 *
 * <p>
 * This allows the {@code ReqCheck} toolchain (PEAtoBoogie etc.) to process countertrace entries the same way it
 * processes regular requirement patterns — the downstream code is completely transparent to the difference.
 * </p>
 *
 * @author University of Freiburg
 */
public class CountertracePattern extends PatternType<CountertracePattern> {

	private static final SrParseScopeGlobally GLOBALLY_SCOPE = new SrParseScopeGlobally();

	private final CounterTrace mCounterTrace;

	public CountertracePattern(final String id, final CounterTrace counterTrace) {
		this(GLOBALLY_SCOPE, id, counterTrace);
	}

	public CountertracePattern(final SrParseScope<?> scope, final String id, final CounterTrace counterTrace) {
		super(scope, id, Collections.emptyList(), Collections.emptyList(), Collections.emptyList());
		mCounterTrace = Objects.requireNonNull(counterTrace);
	}

	/**
	 * @return The pre-built {@link CounterTrace} wrapped by this pattern.
	 */
	public CounterTrace getCounterTrace() {
		return mCounterTrace;
	}

	@Override
	protected List<CounterTrace> transform(final CDD[] cdds, final int[] durations) {
		return Collections.singletonList(mCounterTrace);
	}

	@Override
	public CountertracePattern create(final SrParseScope<?> scope, final String id, final List<CDD> cdds,
			final List<Rational> durations, final List<String> durationNames) {
		return new CountertracePattern(scope, id, mCounterTrace);
	}

	@Override
	public CountertracePattern rename(final String newName) {
		return new CountertracePattern(getScope(), newName, mCounterTrace);
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
		return getId() + ": " + mCounterTrace.toString();
	}

	@Override
	public int hashCode() {
		return Objects.hash(super.hashCode(), mCounterTrace);
	}

	@Override
	public boolean equals(final Object obj) {
		if (!super.equals(obj)) {
			return false;
		}
		final CountertracePattern other = (CountertracePattern) obj;
		return Objects.equals(mCounterTrace, other.mCounterTrace);
	}
}
