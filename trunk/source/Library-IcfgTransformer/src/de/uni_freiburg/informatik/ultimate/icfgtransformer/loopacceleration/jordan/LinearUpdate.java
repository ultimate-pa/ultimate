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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.IPolynomialTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.Monomial;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
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
		for (final Entry<IProgramVar, Term> update : su.getDeterministicAssignment().entrySet()) {
			final Triple<AffineTerm, Set<Term>, String> triple = extractLinearUpdate(mgdScript, termVariablesOfModified,
					update);
			if (triple.getFirst() == null) {
				assert triple.getSecond() == null;
				assert triple.getThird() != null;
				return new Pair<>(null, triple.getThird());
			} else {
				assert triple.getSecond() != null;
				assert triple.getThird() == null;
				updateMap.put(update.getKey().getTermVariable(), triple.getFirst());
				readonlyVariables.addAll(triple.getSecond());
			}
		}
		return new Pair<>(new LinearUpdate(updateMap, readonlyVariables), null);
	}

	private static Triple<AffineTerm, Set<Term>, String> extractLinearUpdate(final ManagedScript mgdScript,
			final Set<TermVariable> termVariablesOfModified, final Entry<IProgramVar, Term> update) {
		// TODO Matthias 20221222: Use AffineTermTransformer
		final IPolynomialTerm polyRhs = (IPolynomialTerm) new PolynomialTermTransformer(mgdScript.getScript())
				.transform(update.getValue());
		final Map<Term, Rational> variables2coeffcient = new HashMap<>();
		final Set<Term> readonlyVariables = new HashSet<>();
		for (final Entry<Monomial, Rational> entry : polyRhs.getMonomial2Coefficient().entrySet()) {
			final Term monomialAsTerm = entry.getKey().toTerm(mgdScript.getScript());
			if (!termVariablesOfModified.contains(monomialAsTerm)) {
				// Monomial is neither an assigned variable nor a havoced variable. In case the
				// monomial contains a subterm that is modified, this is not a linear update,
				// otherwise we consider the monomial as a read-only variable. E.g., a select
				// from a non-modified array at a non-modified index is a typical read-only
				// variable.
				final TermVariable termVariableOfModified = containsTermVariableOfModified(termVariablesOfModified,
						monomialAsTerm);
				if (termVariableOfModified != null) {
					final String errorMessage = String.format(
							"Monomial contains modified variable. Monomial %s, Variable %s", monomialAsTerm,
							termVariableOfModified);
					return new Triple<AffineTerm, Set<Term>, String>(null, null, errorMessage);
				} else {
					readonlyVariables.add(monomialAsTerm);
				}
			}
			variables2coeffcient.put(monomialAsTerm, entry.getValue());
		}
		final AffineTerm affineTerm = new AffineTerm(polyRhs.getSort(), polyRhs.getConstant(), variables2coeffcient);
		return new Triple<AffineTerm, Set<Term>, String>(affineTerm, readonlyVariables, null);
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