/*
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.SimultaneousUpdate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalNestedStore;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.IPolynomialTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.Monomial;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class LinearUpdate {
	Map<TermVariable, AffineTerm> mUpdateMap;
	Set<Term> mReadonlyVariables;

	public LinearUpdate(final Map<TermVariable, AffineTerm> updateMap, final Set<Term> readonlyVariables) {
		super();
		mUpdateMap = updateMap;
		mReadonlyVariables = readonlyVariables;
	}

	public Map<TermVariable, AffineTerm> getUpdateMap() {
		return mUpdateMap;
	}

	public Set<Term> getReadonlyVariables() {
		return mReadonlyVariables;
	}


	public static Pair<LinearUpdate, String> fromSimultaneousUpdate(final ManagedScript mgdScript,
			final SimultaneousUpdate su) {
		final Set<TermVariable> termVariablesOfModified = new HashSet<>();
		for (final Entry<IProgramVar, Term> update : su.getDeterministicAssignment().entrySet()) {
			termVariablesOfModified.add(update.getKey().getTermVariable());
		}
		for (final IProgramVar pv : su.getHavocedVars()) {
			termVariablesOfModified.add(pv.getTermVariable());
		}
		final Set<Term> readonlyVariables = new HashSet<>();
		final Map<TermVariable, AffineTerm> updateMap = new HashMap<>();

		final List<MultiDimensionalSelect> arrayReadsWithFixedIndex = new ArrayList<>();
		for (final Entry<IProgramVar, Term> update : su.getDeterministicAssignment().entrySet()) {
			final UpdateExpression ue = extractLinearUpdate(
					mgdScript, termVariablesOfModified, update.getValue());
			if (ue.getmErrorMessage() != null) {
				return new Pair<>(null, ue.getmErrorMessage());
			} else {
				updateMap.put(update.getKey().getTermVariable(), ue.getmAffineTerm());
				readonlyVariables.addAll(ue.getmReadonlyVariables());
				arrayReadsWithFixedIndex.addAll(ue.getmArrayReads());
			}
		}
		for (final Entry<IProgramVar, MultiDimensionalNestedStore> entry : su.getDeterministicArrayWrites()
				.entrySet()) {
			for (final MultiDimensionalSelect mds : arrayReadsWithFixedIndex) {
				if (mds.getArray().equals(entry.getKey().getTermVariable())) {
					final String errorMessage = String.format(
							"Acceleration would only be sound under the assumption that index %s is different each index in %s",
							mds.getIndex(), entry.getValue().getIndices());
					return new Pair<>(null, errorMessage);
				}
			}
		}
		for (final Entry<IProgramVar, MultiDimensionalNestedStore> update : su.getDeterministicArrayWrites()
				.entrySet()) {
			if (update.getValue().getIndices().size() != 1) {
				throw new UnsupportedOperationException(String.format("Nested stores! Array: %s Indices: %s Values: %s",
						update.getKey(), update.getValue().getIndices(), update.getValue().getValues()));
			}
			final Set<TermVariable> freeVarsOfIndex = update.getValue().getIndices().get(0).getFreeVars();
			freeVarsOfIndex.retainAll(termVariablesOfModified);
			if (!freeVarsOfIndex.isEmpty()) {
				// index is moving
				continue;
			}
			final UpdateExpression quad = extractLinearUpdate(
					mgdScript, termVariablesOfModified, update.getValue().getValues().get(0));
			if (quad.getmErrorMessage() == null) {
				return new Pair<>(null, quad.getmErrorMessage());
			} else {
				final List<MultiDimensionalSelect> arrayReadsWithFixedIndex1 = quad.getmArrayReads();
				for (final Entry<IProgramVar, MultiDimensionalNestedStore> entry : su.getDeterministicArrayWrites()
						.entrySet()) {
					for (final MultiDimensionalSelect mds : arrayReadsWithFixedIndex1) {
						if (mds.getArray().equals(entry.getKey().getTermVariable())) {
							final String errorMessage = String.format(
									"Fixed index update would only be sound under the assumption that index %s and index %s are different. We have %s reads in this update and %s writes in the loop.",
									entry.getValue().getIndices(), mds.getIndex(), arrayReadsWithFixedIndex.size(),
									su.getDeterministicArrayWrites().size());
							return new Pair<>(null, errorMessage);
						}
					}
				}
			}
		}
		return new Pair<>(new LinearUpdate(updateMap, readonlyVariables), null);
	}

	private static UpdateExpression extractLinearUpdate(
			final ManagedScript mgdScript, final Set<TermVariable> termVariablesOfModified, final Term term) {
		final IPolynomialTerm polyRhs = (IPolynomialTerm) new PolynomialTermTransformer(mgdScript.getScript())
				.transform(term);
		final Map<Term, Rational> variables2coeffcient = new HashMap<>();
		final Set<Term> readonlyVariables = new HashSet<>();
		final List<MultiDimensionalSelect> arrayReadsWithFixedIndex = new ArrayList<>();
		for (final Entry<Monomial, Rational> entry : polyRhs.getMonomial2Coefficient().entrySet()) {
			final Term monomialAsTerm = entry.getKey().toTerm(mgdScript.getScript());
			if (termVariablesOfModified.contains(monomialAsTerm)) {
				// Case where monomial is an updated variable
				// Note: I think in this case the variable is always an assigned variable and
				// not a havoced variable. If this variable would be a havoced variable the
				// receiver of this linear update would also be havoced.
				variables2coeffcient.put(monomialAsTerm, entry.getValue());
				continue;
			}
			final TermVariable someOccuringModifiedTermVariable = containsTermVariableOfModified(
					termVariablesOfModified, monomialAsTerm);
			if (someOccuringModifiedTermVariable == null) {
				// Case where monomial is some term that does not contain a modified variable,
				// we will consider this term as a readonly variable
				final MultiDimensionalSelect mds = MultiDimensionalSelect.of(monomialAsTerm);
				if (mds != null) {
					// we have to report this array read because we might need the assumption that
					// its index is different from indices that to which we write
					arrayReadsWithFixedIndex.add(mds);
				} else {
					// If the term is not a select term, are there select terms inside?
					// This occurs hopefully very seldomly and we have to analyze how we are going
					// to handle this case
					final List<MultiDimensionalSelect> innerArrayWrites = MultiDimensionalSelect.extractSelectDeep(term);
					if (!innerArrayWrites.isEmpty()) {
						final String errorMessage = String.format("Yet unsupported inner array read. Monomial %s",
								monomialAsTerm);
						return new UpdateExpression(null, null, null, errorMessage);
					}
				}
				readonlyVariables.add(monomialAsTerm);
				variables2coeffcient.put(monomialAsTerm, entry.getValue());
			} else {
				// Case where monomial is not an updated variable but contains an updated
				// variable. We cannot handle this case, but we want to distinguish several
				// cases in order to return an improved error message.
				if (!entry.getKey().isLinear()) {
					// monomial is nontrivial (i.e., some multiplication of non-literals)
					// nonlinear update that our loop acceleration cannot handle
					final String errorMessage = String.format("Nonlinear update. Monomial %s, Updated variable %s",
							monomialAsTerm, someOccuringModifiedTermVariable);
					return new UpdateExpression(null, null, null, errorMessage);
				}
				final MultiDimensionalSelect mds = MultiDimensionalSelect.of(monomialAsTerm);
				if (mds != null) {
					final Set<TermVariable> freeVarsOfIndex = mds.getIndex().getFreeVars();
					freeVarsOfIndex.retainAll(termVariablesOfModified);
					final String errorMessage = String.format(
							"Non-array update contains array read whose index is moving. Array read %s, modified variable %s",
							mds, freeVarsOfIndex);
					return new UpdateExpression(null, null, null, errorMessage);
				} else {
					final String errorMessage = String.format(
							"Monomial contains modified variable. Monomial %s, Variable %s", monomialAsTerm,
							someOccuringModifiedTermVariable);
					return new UpdateExpression(null, null, null, errorMessage);
				}
			}
		}
		final AffineTerm affineTerm = new AffineTerm(polyRhs.getSort(), polyRhs.getConstant(), variables2coeffcient);
		return new UpdateExpression(affineTerm, readonlyVariables, arrayReadsWithFixedIndex, null);
	}

	private static TermVariable containsTermVariableOfModified(final Set<TermVariable> termVariablesOfModified,
			final Term monomialAsTerm) {
		for (final TermVariable tv : monomialAsTerm.getFreeVars()) {
			if (termVariablesOfModified.contains(tv)) {
				return tv;
			}
		}
		return null;
	}

	public List<LinearUpdate> partition() {
		final UnionFind<Term> uf = new UnionFind<>();
		for (final Entry<TermVariable, AffineTerm> entry : mUpdateMap.entrySet()) {
			uf.findAndConstructEquivalenceClassIfNeeded(entry.getKey());
			for (final Term affineVar : entry.getValue().getVariable2Coefficient().keySet()) {
				uf.findAndConstructEquivalenceClassIfNeeded(affineVar);
				uf.union(entry.getKey(), affineVar);
			}
		}
		final List<LinearUpdate> result = new ArrayList<>();
		for (final Set<Term> eqClass : uf.getAllEquivalenceClasses()) {
			final Map<TermVariable, AffineTerm> newUpdateMap = new HashMap<>();
			for (final Entry<TermVariable, AffineTerm> entry : mUpdateMap.entrySet()) {
				if (eqClass.contains(entry.getKey())) {
					newUpdateMap.put(entry.getKey(), entry.getValue());
				}
			}
			final Set<Term> newReadonlyVariables = new HashSet<>();
			for (final Term roVar : mReadonlyVariables) {
				if (eqClass.contains(roVar)) {
					newReadonlyVariables.add(roVar);
				}
			}
			final LinearUpdate lu = new LinearUpdate(newUpdateMap, newReadonlyVariables);
			result.add(lu);
		}
		return result;
	}

	private static class UpdateExpression {
		private final AffineTerm mAffineTerm;
		private final Set<Term> mReadonlyVariables;
		private final List<MultiDimensionalSelect> mArrayReads;
		private final String mErrorMessage;
		public UpdateExpression(AffineTerm mAffineTerm, Set<Term> mReadonlyVariables,
				List<MultiDimensionalSelect> mArrayReads, String mErrorMessage) {
			super();
			this.mAffineTerm = mAffineTerm;
			this.mReadonlyVariables = mReadonlyVariables;
			this.mArrayReads = mArrayReads;
			this.mErrorMessage = mErrorMessage;
		}
		public AffineTerm getmAffineTerm() {
			return mAffineTerm;
		}
		public Set<Term> getmReadonlyVariables() {
			return mReadonlyVariables;
		}
		public List<MultiDimensionalSelect> getmArrayReads() {
			return mArrayReads;
		}
		public String getmErrorMessage() {
			return mErrorMessage;
		}
	}

}