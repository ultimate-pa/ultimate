/*
 * Copyright (C) 2026 Tobias Kolzer (kolzert@informatik.uni-freiburg.de)
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.pea2boogie.generator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.NonTheorySymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.NonTheorySymbolFinder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;

public class CritPhaseComputer {

	private final Script mScript;
	private final CddToSmt mCddToSmt;

	public record CritPhase(String reqName, Integer index, Term invariant, Term nvc, Term vc, boolean seeping,
			Set<NonTheorySymbol<?>> symbols) {
		public CritPhase(final String reqName, final Integer index, final Term invariant, final Term nvc, final Term vc,
				final boolean seeping) {
			this(reqName, index, invariant, nvc, vc, seeping, new NonTheorySymbolFinder().findNonTheorySymbols(nvc));
		}
	}

	public CritPhaseComputer(final Script script, final CddToSmt cddToSmt) {
		mScript = script;
		mCddToSmt = cddToSmt;
	}

	public Map<Integer, CritPhase> computeCritPhases(final CounterTrace counterTrace, final String reqName) {
		final Map<Integer, CritPhase> results = new HashMap<>();
		final DCPhase[] phases = counterTrace.getPhases();
		final List<Term> seepInvariants = new ArrayList<>(Arrays.asList(mScript.getTheory().mTrue));

		for (int i = phases.length - 2; i >= 0; i--) {
			final DCPhase phase = phases[i];
			final Term invariant = mCddToSmt.toSmt(phase.getInvariant());
			final Term seepInvariant = SmtUtils.and(mScript, seepInvariants.getLast(), invariant);

			// Stop if conjunction of subsequent invariants is unsatisfiable - phase cannot be critical.
			if (LBool.UNSAT == SmtUtils.checkSatTerm(mScript, seepInvariants.getLast())) {
				break;
			}
			if (phase.getBoundType() != CounterTrace.BOUND_GREATER
					&& phase.getBoundType() != CounterTrace.BOUND_GREATEREQUAL) {
				// Phase invariant does imply all subsequent invariants, seeping is unavoidable.
				if (mScript.getTheory().mTrue == SmtUtils.implies(mScript, invariant, seepInvariants.getLast())) {
					seepInvariants.add(seepInvariant);
					continue;
				}
				// Found a critical phase without lower bound.
				final Term vc = seepInvariants.getLast();
				results.put(i, new CritPhase(reqName, i, invariant, SmtUtils.not(mScript, vc), vc, results.size() > 0));
				seepInvariants.add(seepInvariant);
			} else {
				// Found a critical phase with lower bound.
				final Term vc;
				if (mScript.getTheory().mTrue == SmtUtils.implies(mScript, invariant, seepInvariants.getLast())) {
					vc = invariant;
				} else {
					vc = seepInvariants.getLast();
				}
				results.put(i, new CritPhase(reqName, i, invariant, SmtUtils.not(mScript, vc), vc, results.size() > 0));
				break;
			}
		}
		return results;
	}
}
