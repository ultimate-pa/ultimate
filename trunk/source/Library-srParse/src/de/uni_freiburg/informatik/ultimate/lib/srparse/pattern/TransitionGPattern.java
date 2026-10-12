/*
 * Copyright (C) 2025 University of Freiburg
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
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * Globally, if in location {R} then transition to {S} is enabled if guard {V} holds.
 *
 * CDDs (reverse order): V = cdds[0], S = cdds[1], R = cdds[2]
 */
public class TransitionGPattern extends AutomatonPatternType<TransitionGPattern> {

	public TransitionGPattern(final SrParseScope<?> scope, final String id, final List<CDD> cdds,
			final List<Rational> durations, final List<String> durationNames) {
		super(scope, id, cdds, durations, durationNames);
	}

	@Override
	public CDD getSourceLocation() {
		return getCdds().get(2);
	}

	@Override
	public CDD getTargetLocation() {
		return getCdds().get(1);
	}

	@Override
	public CDD getGuard() {
		return getCdds().get(0);
	}

	@Override
	public int getExpectedCddSize() {
		return 3;
	}

	@Override
	public int getExpectedDurationSize() {
		return 0;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		if (getId() != null) {
			sb.append(getId()).append(": ");
		}
		sb.append("if in location \"").append(getCdds().get(2).toBoogieString())
				.append("\" then transition to \"").append(getCdds().get(1).toBoogieString())
				.append("\" is enabled if guard \"").append(getCdds().get(0).toBoogieString())
				.append("\" holds");
		return sb.toString();
	}
}
