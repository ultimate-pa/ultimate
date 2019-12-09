/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 Amalinda Post
 * Copyright (C) 2018 University of Freiburg
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

import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfter;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfterUntil;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBefore;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBetween;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlobally;

/**
 * {scope}, it is always the case that "S" holds.
 *
 * @author Amalinda Post
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class UniversalityPattern extends PatternType {

	public UniversalityPattern(final SrParseScope scope, final String id, final List<CDD> cdds,
			final List<String> durations) {
		super(scope, id, cdds, durations);
	}

	@Override
	public CounterTrace transform(final CDD[] cdds, final int[] durations) {
		final SrParseScope scope = getScope();
		final CDD S = cdds[0];

		if (scope instanceof SrParseScopeGlobally) {
			final CounterTrace ct = counterTrace(phaseT(), phase(S.negate()), phaseT());
			return ct;
		} else if (scope instanceof SrParseScopeBefore) {
			final CDD P = scope.getCdd1();
			final CounterTrace ct = counterTrace(phase(P.negate()), phase(S.negate().and(P.negate())), phaseT());
			return ct;
		} else if (scope instanceof SrParseScopeAfterUntil) {
			final CDD P = scope.getCdd1();
			final CDD Q = scope.getCdd2();
			final CounterTrace ct = counterTrace(phaseT(), phase(P.and(Q.negate())), phase(Q.negate()),
					phase(S.negate().and(Q.negate())), phaseT());
			return ct;
		} else if (scope instanceof SrParseScopeAfter) {
			final CDD P = scope.getCdd1();
			final CounterTrace ct = counterTrace(phaseT(), phase(P), phaseT(), phase(S.negate()), phaseT());
			return ct;
		} else if (scope instanceof SrParseScopeBetween) {
			final CDD P = scope.getCdd1();
			final CDD Q = scope.getCdd2();
			final CounterTrace ct = counterTrace(phaseT(), phase(P.and(Q.negate())), phase(Q.negate()),
					phase(S.negate().and(Q.negate())), phase(Q.negate()), phase(Q), phaseT());
			return ct;
		} else {
			throw new PatternScopeNotImplemented(scope.getClass(), getClass());
		}
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
		sb.append("it is always the case that \"");
		sb.append(getCdds().get(0).toBoogieString());
		sb.append("\" holds");
		return sb.toString();
	}

	@Override
	public PatternType rename(final String newName) {
		return new UniversalityPattern(getScope(), newName, getCdds(), getDuration());
	}

	@Override
	public int getExpectedCddSize() {
		return 1;
	}

	@Override
	public int getExpectedDurationSize() {
		return 0;
	}
}
