/*
 * Copyright (C) 2021 Jonas Werner (wernerj@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Given a set of solutions of a linear system of equations, as set of vectors, compute a vector space basis.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 */
public final class QvasrVectorSpaceBasisConstructor {
	private QvasrVectorSpaceBasisConstructor() {
		// Prevent instantiation of this utility class
	}

	/**
	 * Compute a set of basis vectors that span the set of solutions for a linear system of equations.
	 *
	 * @param script
	 * @param basisVectors
	 * @return
	 */
	public static Rational[][] computeVectorSpaceBasis(final ManagedScript script, final Term[][] basisVectors) {
		final Map<Integer, Term> tvsForColumns = new HashMap<>();
		final Map<Term, Integer> columnsForTvs = new HashMap<>();
		for (int i = 0; i < basisVectors[0].length - 1; i++) {
			final Term newTv = script.constructFreshTermVariable("s", SmtSortUtils.getRealSort(script));
			tvsForColumns.put(i, newTv);
			columnsForTvs.put(newTv, i);
		}

		final Map<Term, List<Term>> equations = new HashMap<>();
		final HashSet<Term> freeVars = new HashSet<>();

		/*
		 * Resubstitute columns to actual variables.
		 */
		final Term[] lastRow = basisVectors[basisVectors.length - 1];
		boolean aIsZero = true;
		for (int i = 0; i < basisVectors.length; i++) {
			if (!QvasrUtils.checkTermEquiv(script, basisVectors[i][basisVectors[0].length - 1],
					script.getScript().decimal("0"))) {
				for (int j = 0; j < basisVectors[i].length - 1; j++) {
					if (!QvasrUtils.checkTermEquiv(script, basisVectors[i][j], script.getScript().decimal("0"))) {
						aIsZero = false;
						break;
					}
				}
			}
		}
		final Term a = script.constructFreshTermVariable("a", SmtSortUtils.getRealSort(script));
		final List<Term> defaultInit = new ArrayList<>();
		if (!aIsZero) {
			defaultInit.add(a);
			freeVars.add(a);
		} else {
			defaultInit.add(script.getScript().decimal("0"));
		}
		tvsForColumns.put(lastRow.length - 1, a);
		columnsForTvs.put(a, lastRow.length - 1);
		equations.put(a, defaultInit);

		/*
		 * Construct equations for each column.
		 */
		for (int j = 0; j < basisVectors.length; j++) {
			final Term[] row = basisVectors[j];
			for (int k = 0; k < row.length - 1; k++) {
				if (!QvasrUtils.checkTermEquiv(script, row[k], script.getScript().decimal("0"))) {
					final Term toBeSolvedFor = tvsForColumns.get(k);
					final List<Term> factors = new ArrayList<>();
					factors.add(SmtUtils.mul(script.getScript(), "*", row[row.length - 1],
							tvsForColumns.get(basisVectors[0].length - 1)));
					for (int l = k + 1; l < row.length - 1; l++) {
						final Term correspondingVar = tvsForColumns.get(l);
						final Term mul = SmtUtils.mul(script.getScript(), "*", row[l], correspondingVar);
						factors.add(SmtUtils.minus(script.getScript(), script.getScript().decimal("0"), mul));
					}
					equations.put(toBeSolvedFor, factors);
					break;
				}
			}
		}
		/*
		 * Free Vars have no solution but can be used as parameters in others.
		 */
		for (final Term var : tvsForColumns.values()) {
			if (!equations.containsKey(var)) {
				final List<Term> defaultInitVars = new ArrayList<>();
				defaultInitVars.add(var);
				equations.put(var, defaultInitVars);
				freeVars.add(var);
			}
		}

		/*
		 * Construct a proto-basisvector for each free variable.
		 */
		final Deque<Term> freeVarStack = new ArrayDeque<>();
		freeVarStack.addAll(freeVars);
		final List<Term[]> vectors = new ArrayList<>();
		while (!freeVarStack.isEmpty()) {
			final Term current = freeVarStack.pop();
			final Map<Term, Term> subMap = new HashMap<>();
			for (final Term var : freeVars) {
				if (var != current) {
					subMap.put(var, script.getScript().decimal("0"));
				} else {
					subMap.put(var, var);
				}
			}
			final Term[] vector = new Term[basisVectors[0].length];
			for (final Entry<Term, List<Term>> solution : equations.entrySet()) {
				final Term tv = solution.getKey();
				final int position = columnsForTvs.get(tv);
				final List<Term> summands = new ArrayList<>();
				for (final Term equation : solution.getValue()) {
					final Term equationUpdated = Substitution.apply(script, subMap, equation);
					summands.add(equationUpdated);
				}
				Term sum;
				if (summands.size() > 1) {
					sum = SmtUtils.sum(script.getScript(), "+", summands.toArray(new Term[summands.size()]));
				} else {
					sum = summands.get(0);
				}
				vector[position] = sum;
			}
			vectors.add(vector);
		}

		/*
		 * Guess a solution.
		 */
		final Map<Term, Term> assignments = new HashMap<>();
		for (final Term var : freeVars) {
			final Term assignment = script.getScript().decimal("1");
			assignments.put(var, assignment);
		}

		final List<Term[]> assignedBasisVectors = new ArrayList<>();
		for (final Term[] vector : vectors) {
			final Term[] vectorAssigned = new Term[vector.length];
			for (int i = 0; i < vector.length; i++) {
				final Term entry = vector[i];
				final Term assigned = Substitution.apply(script, assignments, entry);
				vectorAssigned[i] = assigned;
			}
			assignedBasisVectors.add(vectorAssigned);
		}
		/*
		 * No solutions -> basis is all 0.
		 */
		if (assignedBasisVectors.isEmpty()) {
			return new Rational[0][0];
		}
		return toRational(assignedBasisVectors);
	}

	/**
	 * Transform a List of vectors consisting of {@link ConstantTerm} to an Array of Rationals.
	 *
	 * @param basisVectors
	 * @return
	 */
	private static Rational[][] toRational(final List<Term[]> basisVectors) {
		final Rational[][] basisRational = new Rational[basisVectors.size()][basisVectors.get(0).length];
		for (int i = 0; i < basisVectors.size(); i++) {
			final Term[] basisVector = basisVectors.get(i);
			for (int j = 0; j < basisVector.length; j++) {
				final Term entry = basisVector[j];
				if (!(entry instanceof ConstantTerm)) {
					throw new UnsupportedOperationException("Basisvector must contain only constants!");
				}
				final ConstantTerm entryConst = (ConstantTerm) entry;
				final Rational entryAsRational = (Rational) entryConst.getValue();
				basisRational[i][j] = entryAsRational;
			}
		}
		return basisRational;
	}

	/**
	 * Check whether a given set of solutions for a linear system of equations is consistent. Meaning there are no row
	 * of the form 0 + 0 = 5.
	 *
	 * TODO: May not be needed for Qvasr as we do not get any constants.
	 *
	 * @param script
	 * @param basisVectors
	 * @return
	 */
	private static boolean isConsistent(final ManagedScript script, final Term[][] basisVectors) {
		for (int i = 0; i < basisVectors.length; i++) {
			final Term[] row = basisVectors[i];
			if (!QvasrUtils.checkTermEquiv(script, row[row.length - 1], script.getScript().decimal("0"))) {
				for (int j = 0; j < row.length; j++) {
					if (j == row.length - 1 && row[j] instanceof ConstantTerm) {
						return false;
					}
					if (!QvasrUtils.checkTermEquiv(script, row[j], script.getScript().decimal("0"))) {
						break;
					}
				}
			}
		}
		return true;
	}

}
