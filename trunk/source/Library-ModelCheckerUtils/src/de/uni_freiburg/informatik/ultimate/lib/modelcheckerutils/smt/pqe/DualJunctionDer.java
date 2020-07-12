/*
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.EliminationTask;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.UltimateNormalFormUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryEqualityRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation.AssumptionForSolvability;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Destructive equality resolution (DER) for conjunctions (resp. disjunctions).
 * <br>
 * The DER elimination technique does the following transformation,
 * where t is a term in which x does not occur and [x-->t] denotes the
 * substitution that replaces all occurrences of x by t.
 *
 * <pre>
 * ∃x. x=t ∧ φ(x)   ⟿⟿⟿      φ[x-->t]
 * ∀x. x≠t ∨ φ(x)   ⟿⟿⟿      φ[x-->t]
 * </pre>
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class DualJunctionDer extends DualJunctionQuantifierElimination {

	public DualJunctionDer(final ManagedScript script, final IUltimateServiceProvider services) {
		super(script, services);
	}

	@Override
	public String getName() {
		return "destructive equality resolution";
	}

	@Override
	public String getAcronym() {
		return "DER";
	}

	@Override
	public EliminationResult tryToEliminate(final EliminationTask inputEt) {
		boolean successInLastIteration = false;
		EliminationTask currentEt = inputEt;
		do {
			final EliminationResult er = tryToEliminateOne(currentEt);
			successInLastIteration = (er != null);
			if (er != null) {
				if (!er.getNewEliminatees().isEmpty()) {
					throw new UnsupportedOperationException("not yet implemented");
				}
				if (QuantifierUtils.isDualFiniteJunction(inputEt.getQuantifier(), er.getEliminationTask().getTerm())) {
					return er;
				}
				currentEt = er.getEliminationTask();
			}
		} while (successInLastIteration);
		if (currentEt == inputEt) {
			// only one non-successful iteration
			return null;
		} else {
			return new EliminationResult(currentEt, Collections.emptySet());
		}
	}

	private EliminationResult tryToEliminateOne(final EliminationTask inputEt) {
		for (final TermVariable eliminatee : inputEt.getEliminatees()) {
			final EliminationResult er = tryToEliminate(eliminatee, inputEt);
			if (er != null) {
				return er;
			}
		}
		return null;
	}

	private EliminationResult tryToEliminate(final TermVariable eliminatee, final EliminationTask et) {
		final Term[] dualJuncts = QuantifierUtils.getDualFiniteJunction(et.getQuantifier(), et.getTerm());
		final Pair<Integer, SolvedBinaryRelation> pair = findBestReplacement(et.getQuantifier(), et.getTerm(),
				eliminatee, dualJuncts);
		if (pair == null) {
			return null;
		}
		final List<Term> dualJunctsResult = new ArrayList<>();
		final SolvedBinaryRelation sbr = pair.getSecond();
		if (!sbr.getAssumptionsMap().isEmpty()) {
			for (final Entry<AssumptionForSolvability, Term> entry : sbr.getAssumptionsMap().entrySet()) {
				dualJunctsResult.add(
						QuantifierUtils.negateIfUniversal(mServices, mMgdScript, et.getQuantifier(), entry.getValue()));
			}
		}
		for (int i = 0; i < dualJuncts.length; i++) {
			if (i != pair.getFirst()) {
				final Map<Term, Term> substitutionMapping = Collections.singletonMap(sbr.getLeftHandSide(),
						sbr.getRightHandSide());
				final Substitution substitution = new SubstitutionWithLocalSimplification(mMgdScript,
						substitutionMapping);
				final Term replaced = substitution.transform(dualJuncts[i]);
				assert UltimateNormalFormUtils.respectsUltimateNormalForm(replaced) : "Term not in UltimateNormalForm";
				dualJunctsResult.add(replaced);
			}
		}
		final Term dualJunctionResult = QuantifierUtils.applyDualFiniteConnective(mScript, et.getQuantifier(),
				dualJunctsResult);
		return new EliminationResult(new EliminationTask(et.getQuantifier(), et.getEliminatees(), dualJunctionResult),
				Collections.emptySet());
	}

	private Pair<Integer, SolvedBinaryRelation> findBestReplacement(final int quantifier, final Term term,
			final TermVariable eliminatee, final Term[] dualJuncts) {
		for (int i = 0; i < dualJuncts.length; i++) {
			final SolvedBinaryRelation sbr = solveForSubject(quantifier, eliminatee, dualJuncts[i]);
			if (sbr != null) {
				return new Pair<Integer, SolvedBinaryRelation>(i, sbr);
			}
		}
		return null;
	}

	private SolvedBinaryRelation solveForSubject(final int quantifier, final TermVariable eliminatee, final Term term) {
		final BinaryEqualityRelation ber = BinaryEqualityRelation.convert(term);
		if (ber != null) {
			final SolvedBinaryRelation sfs = ber.solveForSubject(mScript, eliminatee);
			if (sfs != null) {
				return sfs;
			}
		}
		final PolynomialRelation pr = PolynomialRelation.convert(mScript, term);
		if (pr == null) {
			return null;
		}
		final SolvedBinaryRelation sfs = pr.solveForSubject(mScript, eliminatee);
		if (sfs == null) {
			return null;
		}
		if (sfs.getRelationSymbol().equals(QuantifierUtils.getDerOperator(quantifier))) {
			return sfs;
		} else {
			return null;
		}
	}

}
