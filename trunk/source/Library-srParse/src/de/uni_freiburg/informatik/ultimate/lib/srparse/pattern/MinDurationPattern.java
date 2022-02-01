/*
 * Copyright (C) 2018-2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018-2019 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.BoundTypes;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfter;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfterUntil;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBefore;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBetween;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlobally;
import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * {scope}, it is always the case that once "R" becomes satisfied, it holds for at least "c1" time units
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class MinDurationPattern extends PatternType<MinDurationPattern> {
	public MinDurationPattern(final SrParseScope<?> scope, final String id, final List<CDD> cdds,
			final List<Rational> durations, final List<String> durationNames) {
		super(scope, id, cdds, durations, durationNames);
	}

	@Override
	public List<CounterTrace> transform(final CDD[] cdds, final int[] durations) {
		assert cdds.length == 1 && durations.length == 1;

		// P and Q are reserved for scope.
		// R, S, ... are reserved for CDDs, but they are parsed in reverse order.
		final SrParseScope<?> scope = getScope();
		final CDD R = cdds[0];
		final int c1 = durations[0];

		final CounterTrace ct;
		if (scope instanceof SrParseScopeGlobally) {
			ct = counterTrace(phaseT(), phase(R.negate()), phase(R, BoundTypes.LESS, c1), phase(R.negate()), phaseT());
		} else if (scope instanceof SrParseScopeBefore) {
			final CDD P = scope.getCdd1();
			ct = counterTrace(phase(P.negate()), phase(P.negate().and(R.negate())),
					phase(P.negate().and(R), BoundTypes.LESS, c1), phase(P.negate().and(R.negate())), phaseT());
		} else if (scope instanceof SrParseScopeAfterUntil) {
			final CDD P = scope.getCdd1();
			final CDD Q = scope.getCdd2();
			ct = counterTrace(phaseT(), phase(P), phase(Q.negate()), phase(Q.negate().and(R.negate())),
					phase(Q.negate().and(R), BoundTypes.LESS, c1), phase(Q.negate().and(R.negate())), phaseT());
		} else if (scope instanceof SrParseScopeAfter) {
			final CDD P = scope.getCdd1();
			ct = counterTrace(phaseT(), phase(P), phaseT(), phase(R.negate()), phase(R, BoundTypes.LESS, c1),
					phase(R.negate()), phaseT());
		} else if (scope instanceof SrParseScopeBetween) {
			final CDD P = scope.getCdd1();
			final CDD Q = scope.getCdd2();
			ct = counterTrace(phaseT(), phase(P.and(Q.negate())), phase(Q.negate()), phase(Q.negate().and(R.negate())),
					phase(Q.negate().and(R), BoundTypes.LESS, c1), phase(Q.negate().and(R.negate())), phase(Q.negate()),
					phase(Q), phaseT());
		} else {
			throw new PatternScopeNotImplemented(scope.getClass(), getClass());
		}

		return Collections.singletonList(ct);
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		if (getId() != null) {
			sb.append(getId());
			sb.append(": ");
		}
		if (getScope() != null) {
			sb.append(getScope());
		}
		sb.append("it is always the case that once \"");
		sb.append(getCdds().get(0).toBoogieString());
		sb.append("\" becomes satisfied, it holds for at least \"");
		sb.append(getDurations().get(0));
		sb.append("\" time units");
		return sb.toString();
	}

	@Override
	public int getExpectedCddSize() {
		return 1;
	}

	@Override
	public int getExpectedDurationSize() {
		return 1;
	}
}
