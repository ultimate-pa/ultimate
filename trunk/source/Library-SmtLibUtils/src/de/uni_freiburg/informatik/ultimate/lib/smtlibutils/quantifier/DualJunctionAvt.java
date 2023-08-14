/*
 * Copyright (C) 2023 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiIndexArrayUpdate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class DualJunctionAvt extends DualJunctionQuantifierElimination {

	public DualJunctionAvt(final ManagedScript script, final IUltimateServiceProvider services) {
		super(script, services);
	}

	@Override
	public String getName() {
		return "array value transformation";
	}

	@Override
	public String getAcronym() {
		return "AVT";
	}

	@Override
	public EliminationResult tryToEliminate(final EliminationTask inputEt) {

		for (final TermVariable eliminatee : inputEt.getEliminatees()) {

			final Term[] dualFiniteJuncts = QuantifierUtils.getDualFiniteJuncts(inputEt.getQuantifier(),
					inputEt.getTerm());
			final Term replacement = findReplacement(inputEt, eliminatee, dualFiniteJuncts);
			if (replacement != null) {
				final Map<Term, Term> substitutionMapping = Collections.singletonMap(eliminatee, replacement);

				final Term result = Substitution.apply(mMgdScript, substitutionMapping,
						QuantifierUtils.applyDualFiniteConnective(mScript, inputEt.getQuantifier(), dualFiniteJuncts));
				final EliminationTask resultEt = new EliminationTask(inputEt.getQuantifier(), inputEt.getEliminatees(),
						result, inputEt.getContext());
				assert !resultEt.getEliminatees().contains(eliminatee);
				return new EliminationResult(resultEt, Collections.emptySet());
			}
		}

		return null;
	}

	private Term findReplacement(final EliminationTask inputEt, final TermVariable eliminatee,
			final Term[] dualFiniteJuncts) throws AssertionError {
		for (final Term dualFiniteJunct : dualFiniteJuncts) {
			final MultiIndexArrayUpdate miau = MultiIndexArrayUpdate.of(mScript, dualFiniteJunct);
			if (miau == null) {
				continue;
			}
			if (!QuantifierUtils.getDerOperator(inputEt.getQuantifier()).equals(miau.getRelationSymbol())) {
				continue;
			}
			for (int i = miau.getMultiDimensionalNestedStore().getIndices().size() - 1; i >= 0; i--) {
				final Term valueAtI = miau.getMultiDimensionalNestedStore().getValues().get(i);
				if (Arrays.asList(valueAtI.getFreeVars()).contains(eliminatee)) {
					final ArrayIndex idx = miau.getMultiDimensionalNestedStore().getIndices().get(i);
					final Term selectFromNewArray = new MultiDimensionalSelect(miau.getNewArray(), idx).toTerm(mScript);
					final Term derRelation = QuantifierUtils.applyDerOperator(mScript, inputEt.getQuantifier(),
							valueAtI, selectFromNewArray);
					final SolvedBinaryRelation sbr = new DualJunctionDer.DerHelperSbr().solveForSubject(mMgdScript,
							inputEt.getQuantifier(), eliminatee, derRelation,
							inputEt.getContext().getBoundByAncestors());
					if (sbr != null) {
						assert sbr.getLeftHandSide() == eliminatee;
						if (i != miau.getMultiDimensionalNestedStore().getIndices().size() - 1) {
							if (inputEt.getEliminatees().contains(miau.getMultiDimensionalNestedStore().getArray())) {
								throw new AssertionError(String.format(
										"AVT middle case! Array is also Eliminatee. Eliminatee %s Update %s Position %s",
										eliminatee, miau, i));
							} else {
								throw new AssertionError(String.format(
										"AVT middle case! Array is not Eliminatee. Eliminatee %s Update %s Position %s",
										eliminatee, miau, i));
							}
						}
						return sbr.getRightHandSide();
					}
				}
			}
		}
		return null;
	}
}
