/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBefore;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBetween;

/**
 * {scope}, it is always the case that if "U" holds and is succeeded by "T", then "S" eventually holds after "R"
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ResponseChain21Pattern extends PatternType {

	public ResponseChain21Pattern(final SrParseScope scope, final String id, final List<CDD> cdds,
			final List<String> durations) {
		super(scope, id, cdds, durations);
	}

	@Override
	public CounterTrace transform(final CDD[] cdds, final int[] durations) {
		final SrParseScope scope = getScope();
		// note: P and Q are reserved for scope, cdds are parsed in reverse order
		final CDD U = cdds[0];
		final CDD T = cdds[1];
		final CDD S = cdds[2];
		final CDD R = cdds[3];

		final CounterTrace ct;
		if (scope instanceof SrParseScopeBefore) {
			final CDD P = getScope().getCdd1();
			// TODO: fix countertrace
			ct = counterTrace(phase(P.negate()), phase(R.and(P.negate()).and(S.negate())),
					phase(P.negate().and(S).and(R.negate())), phase(P.negate()), phase(P.negate().and(U)),
					phase(P.negate().and(T.negate())), phase(P), phaseT());

			return ct;
		} else if (scope instanceof SrParseScopeBetween) {
			final CDD P = getScope().getCdd1();
			final CDD Q = getScope().getCdd2();
			// TODO: fix countertrace
			ct = counterTrace(phaseT(), phase(P.and(Q.negate())), phase(Q.negate()), phase(Q.negate().and(R)),
					phase(Q.negate().and(S)), phase(Q.negate()), phase(Q.negate().and(U)),
					phase(Q.negate().and(T.negate())), phase(Q), phaseT());
			return ct;
		}
		throw new PatternScopeNotImplemented(scope.getClass(), getClass());
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
		sb.append("it is always the case that if \"");
		sb.append(getCdds().get(3).toBoogieString());
		sb.append("\" holds and is succeeded by \"");
		sb.append(getCdds().get(2).toBoogieString());
		sb.append("\", then \"");
		sb.append(getCdds().get(1).toBoogieString());
		sb.append("\" eventually holds after \"");
		sb.append(getCdds().get(0).toBoogieString());
		sb.append("\"");
		return sb.toString();
	}

	@Override
	public PatternType rename(final String newName) {
		return new ResponseChain21Pattern(getScope(), newName, getCdds(), getDuration());
	}

	@Override
	public int getExpectedCddSize() {
		return 4;
	}

	@Override
	public int getExpectedDurationSize() {
		return 0;
	}
}
