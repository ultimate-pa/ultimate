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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.BinaryEqualityRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.BinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.BinaryRelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Preprocessing step for partial array quantifier elimination. If we have a
 * term of the form <code>arr1 != arr2</ code> (the negation of the form where
 * we can apply DER) we replace it by <code>∃ aux. arr1[aux] != arr2[aux]</
 * code> (Analogously for universal quantification.) Presumes that the input has
 * NNF. Provides all auxiliary variables that have been introduced.
 *
 * @author Matthias Heizmann
 *
 */
public class ArrayEqualityExplicator {

	private final static String AUX_VAR_PREFIX = "antiDerIndex";

	private final List<TermVariable> mNewAuxVars;
	private final Term mResultTerm;

	public ArrayEqualityExplicator(final ManagedScript mgdScript, final int quantifier, final TermVariable eliminatee,
			final Term inputTerm, final List<BinaryEqualityRelation> bers) {
		final List<TermVariable> newAuxVars = new ArrayList();
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final BinaryEqualityRelation ber : bers) {
			if (ber.getRelationSymbol() != BinaryRelation.negateRelation(getDerRelationSymbol(quantifier))) {
				throw new IllegalArgumentException("incompatible relation");
			}
			final Term elementwiseEquality = constructElementwiseEquality(mgdScript, ber.getLhs(), ber.getRhs(),
					newAuxVars);
			final Term replacement;
			if (quantifier == QuantifiedFormula.EXISTS) {
				replacement = elementwiseEquality;
			} else if (quantifier == QuantifiedFormula.FORALL) {
				// does not use SmtUtils method because no simplification possible
				replacement = mgdScript.getScript().term("not", elementwiseEquality);
			} else {
				throw new AssertionError("unknown quantifier");
			}
			substitutionMapping.put(ber.toTerm(mgdScript.getScript()), replacement);
		}
		mResultTerm = new SubstitutionWithLocalSimplification(mgdScript, substitutionMapping).transform(inputTerm);
		mNewAuxVars = newAuxVars;
	}

	private static RelationSymbol getDerRelationSymbol(final int quantifier) {
		if (quantifier == QuantifiedFormula.EXISTS) {
			return RelationSymbol.EQ;
		} else if (quantifier == QuantifiedFormula.FORALL) {
			return RelationSymbol.DISTINCT;
		} else {
			throw new AssertionError("unknown quantifier");
		}
	}

	public Term getResultTerm() {
		return mResultTerm;
	}

	public List<TermVariable> getNewAuxVars() {
		return mNewAuxVars;
	}

	private Term constructElementwiseEquality(final ManagedScript mgdScript, final Term lhsArray, final Term rhsArray,
			final List<TermVariable> newAuxVars) {
		final MultiDimensionalSort mds = new MultiDimensionalSort(lhsArray.getSort());
		final ArrayIndex auxIndex = constructAuxIndex(mgdScript, mds, newAuxVars);
		final Term lhsSelect = SmtUtils.multiDimensionalSelect(mgdScript.getScript(), lhsArray, auxIndex);
		final Term rhsSelect = SmtUtils.multiDimensionalSelect(mgdScript.getScript(), rhsArray, auxIndex);
		// does not use SmtUtils method because no simplification possible
		final Term result = mgdScript.getScript().term("=", lhsSelect, rhsSelect);
		return result;
	}

	private static ArrayIndex constructAuxIndex(final ManagedScript mgdScript, final MultiDimensionalSort mds,
			final List<TermVariable> newAuxVars) {
		final List<Term> indexEntries = new ArrayList<>();
		int offset = 0;
		for (final Sort sort : mds.getIndexSorts()) {
			final TermVariable auxIndex = mgdScript.constructFreshTermVariable(AUX_VAR_PREFIX + "_entry" + offset,
					sort);
			indexEntries.add(auxIndex);
			newAuxVars.add(auxIndex);
			offset++;
		}
		return new ArrayIndex(indexEntries);
	}

}
