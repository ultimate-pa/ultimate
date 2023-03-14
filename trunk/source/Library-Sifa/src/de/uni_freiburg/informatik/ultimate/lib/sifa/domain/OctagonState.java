/*
 * Copyright (C) 2023 Frank Schüssele (schuessf@tf.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.BinaryOperator;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.OctagonRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * State used in {@link OctagonDomain}
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public final class OctagonState implements IAbstractState<OctagonState> {
	public static final OctagonState TOP = new OctagonState(Map.of(), OctagonMatrix.NEW, true);

	/**
	 * Map of numerical variable (ints and reals) names to the index of the corresponding block row/column in the
	 * octagon matrix {@link #mMatrix}. Block row/column i contains the rows/columns 2i and 2i+1.
	 */
	private final Map<Term, Integer> mVarToIndex;

	/** Abstract state for numeric variables (ints and reals). This is the actual octagon. */
	private final OctagonMatrix mMatrix;

	private final boolean mAllVarsAreInt;

	private OctagonState(final Map<Term, Integer> varToIndex, final OctagonMatrix matrix, final boolean allVarsAreInt) {
		mVarToIndex = varToIndex;
		mMatrix = matrix;
		mAllVarsAreInt = allVarsAreInt;
	}

	/**
	 * Constructs a OctagonState from a given collection of conjuncts
	 */
	public static OctagonState from(final Term[] conjuncts, final Script script) {
		final List<OctagonRelation> octRelations = new ArrayList<>();
		final Set<Term> vars = new HashSet<>();
		for (final Term conjunct : conjuncts) {
			final PolynomialRelation polynomial = PolynomialRelation.of(script, conjunct);
			if (polynomial == null) {
				continue;
			}
			final OctagonRelation octRel = OctagonRelation.from(polynomial);
			if (octRel == null) {
				continue;
			}
			octRelations.add(octRel);
			vars.add(octRel.getVar1());
			vars.add(octRel.getVar2());
		}
		boolean allVarsAreInt = true;
		final List<Term> sortedVars =
				vars.stream().sorted((x, y) -> x.toString().compareTo(y.toString())).collect(Collectors.toList());
		final Map<Term, Integer> varToIndex =
				IntStream.range(0, vars.size()).boxed().collect(Collectors.toMap(sortedVars::get, x -> x));
		final OctagonMatrix resultMatrix = new OctagonMatrix(varToIndex.size());
		for (final OctagonRelation octRel : octRelations) {
			allVarsAreInt &= !SmtSortUtils.isRealSort(octRel.getVar1().getSort());
			resultMatrix.processRelation(octRel, varToIndex);
		}
		return new OctagonState(varToIndex, resultMatrix, allVarsAreInt);
	}

	private Term[] getIndexToTermArray() {
		final Term[] result = new Term[mVarToIndex.size()];
		for (final Entry<Term, Integer> entry : mVarToIndex.entrySet()) {
			result[entry.getValue()] = entry.getKey();
		}
		return result;
	}

	@Override
	public Term toTerm(final Script script) {
		return SmtUtils.and(script, cachedSelectiveClosure().getTerm(script, getIndexToTermArray()));
	}

	@Override
	public String toString() {
		return Arrays.toString(getIndexToTermArray()) + "\n" + mMatrix.toString();
	}

	private OctagonMatrix cachedSelectiveClosure() {
		return mAllVarsAreInt ? mMatrix.cachedTightClosure() : mMatrix.cachedStrongClosure();
	}

	private OctagonState applyMergeOperator(final OctagonState other, final BinaryOperator<OctagonMatrix> matrixOp) {
		final Map<Term, Integer> varToIndex = new HashMap<>();
		final Set<Term> allVars = DataStructureUtils.union(mVarToIndex.keySet(), other.mVarToIndex.keySet());
		final int[] copyInstructions1 = new int[allVars.size()];
		final int[] copyInstructions2 = new int[allVars.size()];
		int lastIndex = mVarToIndex.size();
		boolean allVarsAreInt = mAllVarsAreInt;
		for (final Term variable : allVars) {
			final int index1 = mVarToIndex.getOrDefault(variable, -1);
			final int index2 = other.mVarToIndex.getOrDefault(variable, -1);
			if (index1 != -1) {
				varToIndex.put(variable, index1);
				copyInstructions1[index1] = index1;
				copyInstructions2[index1] = index2;
			} else {
				varToIndex.put(variable, lastIndex);
				copyInstructions1[lastIndex] = index1;
				copyInstructions2[lastIndex] = index2;
				lastIndex++;
				if (allVarsAreInt && SmtSortUtils.isRealSort(variable.getSort())) {
					allVarsAreInt = false;
				}
			}
		}
		final OctagonMatrix matrix1 = rearrangeIfNecessary(bestAvailableClosure(), copyInstructions1);
		final OctagonMatrix matrix2 = rearrangeIfNecessary(other.bestAvailableClosure(), copyInstructions2);
		return new OctagonState(varToIndex, matrixOp.apply(matrix1, matrix2), allVarsAreInt);
	}

	private static OctagonMatrix rearrangeIfNecessary(final OctagonMatrix matrix, final int[] copyInstructions) {
		for (int i = 0; i < copyInstructions.length; i++) {
			if (copyInstructions[i] != i) {
				return matrix.rearrange(copyInstructions);
			}
		}
		// The copyInstructions are simply the identity, so there is no need to rearrange
		return matrix;
	}

	private OctagonMatrix bestAvailableClosure() {
		if (mAllVarsAreInt && mMatrix.hasCachedTightClosure()) {
			return mMatrix.cachedTightClosure();
		} else if (mMatrix.hasCachedStrongClosure()) {
			return mMatrix.cachedStrongClosure();
		}
		return mMatrix;
	}

	@Override
	public OctagonState widen(final OctagonState other) {
		// TODO: Make the widening operator a setting?
		return applyMergeOperator(other, OctagonMatrix::widenSimple);
	}

	@Override
	public OctagonState join(final OctagonState other) {
		return applyMergeOperator(other, OctagonMatrix::max);
	}

	@Override
	public boolean isBottom() {
		return cachedSelectiveClosure().hasNegativeSelfLoop();
	}
}
