/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalNestedStore;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe.EqualityInformation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class ArrayIndexEqualityUtils {

	/**
	 * Add equality information for term that are obtained from context by only
	 * looking at (dis)eqality terms.
	 *
	 * @return
	 * @return true if an inconsitency was detected
	 */
	public static boolean addComplimentaryEqualityInformation(final Script script, final int quantifier,
			final Term[] context, final Term term, final ThreeValuedEquivalenceRelation<Term> equalityInformation) {
		equalityInformation.addElement(term);
		final Pair<Set<Term>, Set<Term>> indexEqual = EqualityInformation.getEqTerms(script, term, context, null);
		Set<Term> derTerms;
		Set<Term> antiDerTerms;
		if (quantifier == QuantifiedFormula.EXISTS) {
			derTerms = indexEqual.getFirst();
			antiDerTerms = indexEqual.getSecond();
		} else if (quantifier == QuantifiedFormula.FORALL) {
			derTerms = indexEqual.getSecond();
			antiDerTerms = indexEqual.getFirst();
		} else {
			throw new AssertionError("unknown quantifier");
		}
		for (final Term equal : derTerms) {
			equalityInformation.addElement(equal);
			equalityInformation.reportEquality(term, equal);
			if (equalityInformation.isInconsistent()) {
				return true;
			}
		}
		for (final Term disequal : antiDerTerms) {
			equalityInformation.addElement(disequal);
			equalityInformation.reportDisequality(term, disequal);
			if (equalityInformation.isInconsistent()) {
				return true;
			}
		}
		return false;
	}

	static ThreeValuedEquivalenceRelation<Term> collectComplimentaryEqualityInformation(final Script script,
			final int quantifier, final Term preprocessedInput, final List<MultiDimensionalSelect> selectTerms,
			final List<MultiDimensionalNestedStore> stores) {
		final ThreeValuedEquivalenceRelation<Term> equalityInformation = new ThreeValuedEquivalenceRelation<>();
		final Term[] context = QuantifierUtils.getXjunctsInner(quantifier, preprocessedInput);
		boolean inconsistencyDetected = false;
		for (final MultiDimensionalSelect selectTerm : selectTerms) {
			for (final Term entry : selectTerm.getIndex()) {
				inconsistencyDetected |= addComplimentaryEqualityInformation(script, quantifier, context, entry,
						equalityInformation);
				if (inconsistencyDetected) {
					return null;
				}
			}
			inconsistencyDetected |= addComplimentaryEqualityInformation(script, quantifier, context, selectTerm.toTerm(script),
					equalityInformation);
			if (inconsistencyDetected) {
				return null;
			}

		}
		for (final MultiDimensionalNestedStore arrayStore : stores) {
			for (final ArrayIndex ai : arrayStore.getIndices()) {
				for (final Term entry : ai) {
					inconsistencyDetected |= addComplimentaryEqualityInformation(script, quantifier, context,
							entry, equalityInformation);
					if (inconsistencyDetected) {
						return null;
					}
				}
			}
			for (final Term value : arrayStore.getValues()) {
				inconsistencyDetected |= addComplimentaryEqualityInformation(script, quantifier, context,
						value, equalityInformation);
				if (inconsistencyDetected) {
					return null;
				}
			}
		}
		return equalityInformation;
	}

	static ThreeValuedEquivalenceRelation<Term> analyzeIndexEqualities(final Script script, final ArrayIndex selectIndex,
			final ArrayIndex storeIndex, final int quantifier, final Term[] context) {
		final ThreeValuedEquivalenceRelation<Term> tver = new ThreeValuedEquivalenceRelation<>();
		for (final Term term : selectIndex) {
			addComplimentaryEqualityInformation(script, quantifier, context, term, tver);
		}
		for (final Term term : storeIndex) {
			addComplimentaryEqualityInformation(script, quantifier, context, term, tver);
		}
		return tver;
	}

	private static Term getIndexOfSelect(final ApplicationTerm appTerm) {
		assert (appTerm.getParameters().length == 2) : "no select";
		assert (appTerm.getFunction().getName().equals("select")) : "no select";
		return appTerm.getParameters()[1];
	}
}
