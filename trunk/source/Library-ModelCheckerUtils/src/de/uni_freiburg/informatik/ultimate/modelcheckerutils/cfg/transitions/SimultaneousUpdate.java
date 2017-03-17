/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 *
 * @author heizmann@informatik.uni-freiburg.de
 */
public class SimultaneousUpdate {

	Map<IProgramVar, Term> mUpdatedVars = new HashMap<>();
	Set<IProgramVar> mHavocedVars = new HashSet<>();

	public SimultaneousUpdate(final TransFormula tf) {
		final Map<TermVariable, IProgramVar> inVarsReverseMapping = constructReverseMapping(tf.getInVars());
		final Map<TermVariable, IProgramVar> outVarsReverseMapping = constructReverseMapping(tf.getOutVars());
		final Term[] conjuncts = SmtUtils.getConjuncts(tf.getFormula());
		final HashRelation<IProgramVar, Term> pv2conjuncts = new HashRelation<>();
		for (final Term conjunct : conjuncts) {
			for (final TermVariable tv : conjunct.getFreeVars()) {
				final IProgramVar pv = outVarsReverseMapping.get(tv);
				if (pv != null) {
					pv2conjuncts.addPair(pv, conjunct);
				}
			}
		}
		final Set<IProgramVar> allProgVars = new HashSet<>();
		allProgVars.addAll(tf.getInVars().keySet());
		allProgVars.addAll(tf.getOutVars().keySet());
		for (final IProgramVar pv : allProgVars) {
			if (tf.isHavocedOut(pv)) {
				mHavocedVars.add(pv);
			} else {
				final Set<Term> pvContainingConjuncts = pv2conjuncts.getImage(pv);
				if (pvContainingConjuncts.isEmpty()) {
					if (tf.getInVars().get(pv) != tf.getOutVars().get(pv)) {
						throw new AssertionError("in and out have to be similar");
					}
				} else if (pvContainingConjuncts.size() == 1) {
					// extract
				} else {
					throw new IllegalArgumentException("cannot bring into simultaneous update form " + pv
							+ "'s outvar occurs in several conjuncts.");
				}
			}
		}

	}

	public static <V, K> Map<V, K> constructReverseMapping(final Map<K, V> map) {
		return map.entrySet().stream().collect(Collectors.toMap(Entry::getValue, c -> c.getKey()));
	}
}
