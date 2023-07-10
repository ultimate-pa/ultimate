/*
 /*
 /*
 /*
 * Copyright (C) 2023 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2023 Xinyu Jiang
 * Copyright (C) 2023 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.CommuhashUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * 
 * @author Xinyu Jiang
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class DualJunctionSgi extends DualJunctionQuantifierElimination {

	public DualJunctionSgi(final ManagedScript script, final IUltimateServiceProvider services) {
		super(script, services);
	}

	@Override
	public String getName() {
		return "syntax guided instantiation";
	}

	@Override
	public String getAcronym() {
		return "SGI";
	}

	@Override
	public EliminationResult tryToEliminate(final EliminationTask inputEt) {
		final Term[] candidateDualFiniteJuncts = QuantifierUtils.getDualFiniteJuncts(inputEt.getQuantifier(),
				inputEt.getContext().getCriticalConstraint());
		final Term[] qSubformulaDualFiniteJuncts =
				QuantifierUtils.getDualFiniteJuncts(inputEt.getQuantifier(), inputEt.getTerm());
		final List<Term> candidateConjunctsList = Arrays.asList(candidateDualFiniteJuncts);
		final List<Term> qSubformulaConjunctsList = Arrays.asList(qSubformulaDualFiniteJuncts);

		final List<Map<TermVariable, Term>> finalresult =
				instantiateCartesian(inputEt.getEliminatees(), qSubformulaConjunctsList, candidateConjunctsList);
		if (finalresult != null) {
			return new EliminationResult(inputEt.update(mScript.term("true")), Collections.emptySet());
		}
		return null;
	}

	public List<Map<TermVariable, Term>> instantiateCartesian(final Set<TermVariable> instantiatees,
			final List<Term> qsubformulas, final List<Term> candidates) {
		boolean found = false;
		final List<Map<TermVariable, Term>> mapList = new ArrayList<>();
		rotationLoop: for (int r = 0; r < qsubformulas.size(); r++) {
			Collections.rotate(qsubformulas, 1);
			List<Map<TermVariable, Term>> mapForThisRotation = new ArrayList<>();
			final Set<Integer> bannedcandidates = new HashSet<>();
			boolean foundInRotation = false;
			for (int i = 0; i < qsubformulas.size(); i++) {
				List<Map<TermVariable, Term>> res = null;
				for (int j = 0; j < candidates.size(); j++) {
					if (bannedcandidates.contains(j)) {
						continue;
					}
					res = matchExpression(instantiatees, qsubformulas.get(i), candidates.get(j));
					if (res != null) {
						final List<Map<TermVariable, Term>> mapForThisMatch = mergeAllMaps(mapForThisRotation, res);
						if (mapForThisMatch == null) {
							continue;
						}
						mapForThisRotation = mapForThisMatch;
						foundInRotation = true;
						bannedcandidates.add(j);
						break;
					}
				}
				if (res == null) {
					continue rotationLoop;
				}
			}
			found = found || foundInRotation;
			mapList.addAll(mapForThisRotation);
		}
		if (found) {

			return mapList;
		}
		return null;
	}

	public List<Map<TermVariable, Term>> instantiatePairwise(final Set<TermVariable> instantiatees,
			final List<Term> qsubformulas, final List<Term> candidates) {
		List<Map<TermVariable, Term>> mapList = new ArrayList<>();
		for (int i = 0; i < qsubformulas.size(); i++) {
			List<Map<TermVariable, Term>> res = null;

			res = matchExpression(instantiatees, qsubformulas.get(i), candidates.get(i));
			if (res != null) {
				mapList = mergeAllMaps(mapList, res);
				if (mapList == null) {
					return null;
				}
			} else {
				return null;
			}
		}
		return mapList;
	}

	public List<Map<TermVariable, Term>> mergeAllMaps(final List<Map<TermVariable, Term>> mergedmap,
			final List<Map<TermVariable, Term>> tobemerged) {
		final List<Map<TermVariable, Term>> finalMergedMap = new ArrayList<>();
		if (mergedmap.isEmpty()) {
			finalMergedMap.addAll(tobemerged);
			return finalMergedMap;
		}
		for (int i = 0; i < mergedmap.size(); i++) {
			for (int j = 0; j < tobemerged.size(); j++) {
				final Map<TermVariable, Term> mergeTwoMapsResult = mergeTwoMaps(mergedmap.get(i), tobemerged.get(j));
				if (mergeTwoMapsResult == null) {
					continue;
				}
				finalMergedMap.add(mergeTwoMapsResult);
			}
		}
		if (finalMergedMap.isEmpty()) {
			return null;
		}
		return finalMergedMap;
	}

	public Map<TermVariable, Term> mergeTwoMaps(final Map<TermVariable, Term> fromMerged,
			final Map<TermVariable, Term> toMerge) {
		final Map<TermVariable, Term> mergedmap = new HashMap<>();
		for (final TermVariable key : fromMerged.keySet()) {
			if ((toMerge.containsKey(key)) && (fromMerged.get(key) != toMerge.get(key))) {
				return null;
			}
		}
		mergedmap.putAll(fromMerged);
		mergedmap.putAll(toMerge);
		return mergedmap;
	}

	public List<Map<TermVariable, Term>> matchExpression(final Set<TermVariable> instantiatees, final Term qsubformula,
			final Term candidate) {
		if ((qsubformula instanceof ApplicationTerm) && (candidate instanceof ApplicationTerm)) {
			final ApplicationTerm qsubformulaAppTerm = (ApplicationTerm) qsubformula;
			final ApplicationTerm candidateAppTerm = (ApplicationTerm) candidate;
			if (qsubformulaAppTerm.getFunction() == candidateAppTerm.getFunction()) {
				final Boolean isCommutative =
						CommuhashUtils.isKnownToBeCommutative(qsubformulaAppTerm.getFunction().getName());
				List<Map<TermVariable, Term>> res;

				if (Arrays.asList(qsubformulaAppTerm.getParameters()).size() == Arrays
						.asList(candidateAppTerm.getParameters()).size()) {
					if (isCommutative) {
						res = instantiateCartesian(instantiatees, Arrays.asList(qsubformulaAppTerm.getParameters()),
								Arrays.asList(candidateAppTerm.getParameters()));
					} else {
						res = instantiatePairwise(instantiatees, Arrays.asList(qsubformulaAppTerm.getParameters()),
								Arrays.asList(candidateAppTerm.getParameters()));
					}
					return res;
				}
			} else {
				return null;
			}
		}

		if (qsubformula instanceof TermVariable) {
			if (instantiatees.contains(qsubformula)) {
				return List.of(Collections.singletonMap((TermVariable) qsubformula, candidate));
			}
			if (qsubformula == candidate) {
				return List.of(Collections.emptyMap());
			}
			if (qsubformula != candidate) {
				return null;
			}
		}

		if ((qsubformula instanceof ConstantTerm) && (candidate instanceof ConstantTerm)
				&& (((ConstantTerm) qsubformula).getValue() == ((ConstantTerm) candidate).getValue())) {
			return List.of(Collections.emptyMap());
			// find alternative to getValue
		}
		return null;
	}
}