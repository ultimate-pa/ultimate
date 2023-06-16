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

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.CommuhashUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

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
		if (inputEt.getQuantifier() == QuantifiedFormula.FORALL) {
			throw new UnsupportedOperationException("Universal Quantifier not yet implemented");
		}
		final Term[] candidateConjuncts = QuantifierUtils.getDualFiniteJuncts(inputEt.getQuantifier(),
				inputEt.getContext().getCriticalConstraint());
		final Term[] qSubformulaConjuncts =
				QuantifierUtils.getDualFiniteJuncts(inputEt.getQuantifier(), inputEt.getTerm());
		final List<Term> candidateConjunctsList = Arrays.asList(candidateConjuncts);
		final List<Term> qSubformulaConjunctsList = Arrays.asList(qSubformulaConjuncts);

		for (int i = 0; i < candidateConjunctsList.size(); i++) {
			Collections.rotate(candidateConjunctsList, 1);
			final Pair<Boolean, Map<TermVariable, Term>> finalresult =
					instantiateCartesian(inputEt.getEliminatees(), qSubformulaConjunctsList, candidateConjunctsList);
			if (finalresult.getFirst()) {
				assert finalresult.getSecond().size() == inputEt.getEliminatees().size();
				return new EliminationResult(inputEt.update(mScript.term("true")), Collections.emptySet());
			}
		}
		return null;
	}

	/// boolean with if parameter numbers are equivalent
	public Pair<Boolean, Map<TermVariable, Term>> instantiateCartesian(final Set<TermVariable> instantiatees,
			final List<Term> qsubformulas, final List<Term> candidates) {
		final Set<Integer> bannedcandidates = new HashSet<>();
		final Map<TermVariable, Term> mergedmap = new HashMap<>();
		for (int i = 0; i < qsubformulas.size(); i++) {
			Pair<Boolean, Map<TermVariable, Term>> res = new Pair<>(false, null);
			candidateloop: for (int j = 0; j < candidates.size(); j++) {
				if (bannedcandidates.contains(j)) {
					continue;
				}
				res = matchExpression(instantiatees, qsubformulas.get(i), candidates.get(j));
				if (res.getFirst()) {
					/// extractmap merging to new method
					final Map<TermVariable, Term> mapFromCandidates = res.getSecond();
					for (final Entry<TermVariable, Term> entry : mapFromCandidates.entrySet()) {
						if (mergedmap.containsKey(entry.getKey())
								&& !(mergedmap.get(entry.getKey()) == entry.getValue())) {
							res = new Pair<>(false, null);
							continue candidateloop;
						}
						mergedmap.put(entry.getKey(), entry.getValue());
					}
					bannedcandidates.add(j);
					break;
				}
			}
			if (!res.getFirst()) {
				return new Pair<>(false, null);
			}
		}
		return new Pair<>(true, mergedmap);
	}

	public Pair<Boolean, Map<TermVariable, Term>> instantiatePairwise(final Set<TermVariable> instantiatees,
			final List<Term> qsubformulas, final List<Term> candidates) {
		final Map<TermVariable, Term> mergedmap = new HashMap<>();
		for (int i = 0; i < qsubformulas.size(); i++) {
			Pair<Boolean, Map<TermVariable, Term>> res = new Pair<>(false, null);

			res = matchExpression(instantiatees, qsubformulas.get(i), candidates.get(i));
			if (res.getFirst()) {
				final Map<TermVariable, Term> mapFromCandidates = res.getSecond();
				for (final Entry<TermVariable, Term> entry : mapFromCandidates.entrySet()) {
					if (mergedmap.containsKey(entry.getKey()) && !(mergedmap.get(entry.getKey()) == entry.getValue())) {
						return new Pair<>(false, null);
					}
					mergedmap.put(entry.getKey(), entry.getValue());
				}

			} else {
				return new Pair<>(false, null);
			}
		}
		return new Pair<>(true, mergedmap);

	}

	public Pair<Boolean, Map<TermVariable, Term>> matchExpression(final Set<TermVariable> instantiatees,
			final Term qsubformula, final Term candidate) {

		if ((qsubformula instanceof ApplicationTerm) && (candidate instanceof ApplicationTerm)) {
			final ApplicationTerm qsubformulaAppTerm = (ApplicationTerm) qsubformula;
			final ApplicationTerm candidateAppTerm = (ApplicationTerm) candidate;
			if (qsubformulaAppTerm.getFunction() == candidateAppTerm.getFunction()) {
				/// final FunctionSymbol functiontest = qsubformulaAppTerm.getFunction(); /// testing
				final Boolean isCommutative =
						CommuhashUtils.isKnownToBeCommutative(qsubformulaAppTerm.getFunction().getName());
				Pair<Boolean, Map<TermVariable, Term>> res;

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
				return new Pair<>(false, null);
			}
		}

		if (qsubformula instanceof TermVariable) {
			if (instantiatees.contains(qsubformula)) {
				return new Pair<>(true, Collections.singletonMap((TermVariable) qsubformula, candidate));
			}
			if (qsubformula == candidate) {
				return new Pair<>(true, Collections.emptyMap());
			}
			if (!(qsubformula == candidate)) {
				return new Pair<>(false, null);
			}
		}

		if ((qsubformula instanceof ConstantTerm) && (candidate instanceof ConstantTerm)
				&& (((ConstantTerm) qsubformula).getValue() == ((ConstantTerm) candidate).getValue())) {
			return new Pair<>(true, Collections.emptyMap());
			// find alternative to getValue
		}
		return new Pair<>(false, null);
	}

}