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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayIndex;
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
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Quad;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

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
			final Quad<AffineTerm, Set<Term>, List<MultiDimensionalSelect>, String> quad = extractLinearUpdate(
					mgdScript, termVariablesOfModified, update.getValue());
			if (quad.getFirst() == null) {
				assert quad.getSecond() == null;
				assert quad.getThird() == null;
				assert quad.getFourth() != null;
				return new Pair<>(null, quad.getFourth());
			} else {
				assert quad.getSecond() != null;
				assert quad.getThird() != null;
				assert quad.getFourth() == null;
				updateMap.put(update.getKey().getTermVariable(), quad.getFirst());
				readonlyVariables.addAll(quad.getSecond());
				arrayReadsWithFixedIndex.addAll(quad.getThird());
			}
		}
		for (final Triple<IProgramVar, ArrayIndex, Term> entry : su.getDeterministicArrayWrites().entrySet()) {
			for (final MultiDimensionalSelect mds : arrayReadsWithFixedIndex) {
				if (mds.getArray().equals(entry.getFirst().getTermVariable())) {
					final String errorMessage = String.format(
							"Acceleration would only be sound under the assumption that index %s and index %s are different",
							entry.getSecond(), mds.getIndex());
					return new Pair<>(null, errorMessage);
				}
			}
		}
		for (final Triple<IProgramVar, ArrayIndex, Term> update : su.getDeterministicArrayWrites().entrySet()) {
			final Set<TermVariable> freeVarsOfIndex = update.getSecond().getFreeVars();
			freeVarsOfIndex.retainAll(termVariablesOfModified);
			if (!freeVarsOfIndex.isEmpty()) {
				// index is moving
				continue;
			}
			final Quad<AffineTerm, Set<Term>, List<MultiDimensionalSelect>, String> quad = extractLinearUpdate(
					mgdScript, termVariablesOfModified, update.getThird());
			if (quad.getFirst() == null) {
				assert quad.getSecond() == null;
				assert quad.getThird() == null;
				assert quad.getFourth() != null;
				return new Pair<>(null, quad.getFourth());
			} else {
				assert quad.getSecond() != null;
				assert quad.getThird() != null;
				assert quad.getFourth() == null;
				final List<MultiDimensionalSelect> arrayReadsWithFixedIndex1 = quad.getThird();
				for (final Triple<IProgramVar, ArrayIndex, Term> entry : su.getDeterministicArrayWrites().entrySet()) {
					for (final MultiDimensionalSelect mds : arrayReadsWithFixedIndex1) {
						if (mds.getArray().equals(entry.getFirst().getTermVariable())) {
							final String errorMessage = String.format(
									"Fixed index update would only be sound under the assumption that index %s and index %s are different. We have %s reads in this update and %s writes in the loop.",
									entry.getSecond(), mds.getIndex(), arrayReadsWithFixedIndex.size(),
									su.getDeterministicArrayWrites().size());
							return new Pair<>(null, errorMessage);
						}
					}
				}
			}
		}
		return new Pair<>(new LinearUpdate(updateMap, readonlyVariables), null);
	}

	private static Quad<AffineTerm, Set<Term>, List<MultiDimensionalSelect>, String> extractLinearUpdate(
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
				final MultiDimensionalSelect mds = MultiDimensionalSelect.convert(monomialAsTerm);
				if (mds != null) {
					// we have to report this array read because we might need the assumption that
					// its index is different from indices that to which we write
					arrayReadsWithFixedIndex.add(mds);
				} else {
					// If the term is not a select term, are there select terms inside?
					// This occurs hopefully very seldomly and we have to analyze how we are going
					// to handle this case
					final List<MultiDimensionalSelect> innerArrayWrites = MultiDimensionalSelect.extractSelectDeep(term,
							true);
					if (!innerArrayWrites.isEmpty()) {
						final String errorMessage = String.format("Yet unsupported inner array read. Monomial %s",
								monomialAsTerm);
						return new Quad<AffineTerm, Set<Term>, List<MultiDimensionalSelect>, String>(null, null, null,
								errorMessage);
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
					return new Quad<AffineTerm, Set<Term>, List<MultiDimensionalSelect>, String>(null, null, null,
							errorMessage);
				}
				final MultiDimensionalSelect mds = MultiDimensionalSelect.convert(monomialAsTerm);
				if (mds != null) {
					final Set<TermVariable> freeVarsOfIndex = mds.getIndex().getFreeVars();
					freeVarsOfIndex.retainAll(termVariablesOfModified);
					final String errorMessage = String.format(
							"Update contains array read whose index is moving. Array read %s, modified variable %s",
							mds, freeVarsOfIndex);
					return new Quad<AffineTerm, Set<Term>, List<MultiDimensionalSelect>, String>(null, null, null,
							errorMessage);
				} else {
					final String errorMessage = String.format(
							"Monomial contains modified variable. Monomial %s, Variable %s", monomialAsTerm,
							someOccuringModifiedTermVariable);
					return new Quad<AffineTerm, Set<Term>, List<MultiDimensionalSelect>, String>(null, null, null,
							errorMessage);
				}
			}
		}
		final AffineTerm affineTerm = new AffineTerm(polyRhs.getSort(), polyRhs.getConstant(), variables2coeffcient);
		return new Quad<>(affineTerm, readonlyVariables, arrayReadsWithFixedIndex, null);
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
}