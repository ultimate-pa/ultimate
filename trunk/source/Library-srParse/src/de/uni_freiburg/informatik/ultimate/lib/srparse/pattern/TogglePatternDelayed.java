/*
 * Copyright (C) 2019 Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
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
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.BoundTypes;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.reqcheck.PatternToPEA;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlob;

/**
 * "{scope}, if S holds then P toggles T after at most c1 time units."
 *
 *
 */
public class TogglePatternDelayed extends PatternType {

	public TogglePatternDelayed(final SrParseScope scope, final String id, final List<CDD> cdds,
			final List<String> durations) {
		super(scope, id, cdds, durations);
	}

	@Override
	protected PhaseEventAutomata transform(final PatternToPEA peaTrans, final Map<String, Integer> id2bounds) {
		final CDD[] cdds = getCddsAsArray();
		final int[] durations = getDurationsAsIntArray(id2bounds);
		assert cdds.length == 3 && durations.length == 1;

		final SrParseScope scope = getScope();
		final CDD S = cdds[0];
		final CDD P = cdds[1];
		final CDD T = cdds[2];
		final int c1 = durations[0];

		if (scope instanceof SrParseScopeGlob) {
			final CounterTrace ct = counterTrace(phaseT(), phase(P.and(S)),
					phase(P.negate(), BoundTypes.GREATEREQUAL, c1), phase(P.negate().and(T.negate())), phaseT());
			return compile(peaTrans, ct);
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
		sb.append(getCdds().get(0).toBoogieString());
		sb.append("\" holds then \"");
		sb.append(getCdds().get(1).toBoogieString());
		sb.append("\" toggles \"");
		sb.append(getCdds().get(2).toBoogieString());
		sb.append("\" at most \"");
		sb.append(getDuration().get(0));
		sb.append("\" time units later");
		return sb.toString();
	}

	@Override
	public PatternType rename(final String newName) {
		return new TogglePatternDelayed(getScope(), newName, getCdds(), getDuration());

	}

}
