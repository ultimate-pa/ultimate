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

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.BinaryOperator;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.octagon.OctMatrix;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.octagon.OctValue;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.OctagonRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
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
	public static final OctagonState TOP = new OctagonState(Map.of(), OctMatrix.NEW, true);

	/**
	 * Map of numerical variable (ints and reals) names to the index of the corresponding block row/column in the
	 * octagon matrix {@link #mNumericAbstraction}. Block row/column i contains the rows/columns 2i and 2i+1.
	 */
	private final Map<Term, Integer> mMapNumericVarToIndex;

	/** Abstract state for numeric variables (ints and reals). This is the actual octagon. */
	private final OctMatrix mNumericAbstraction;

	private final boolean mAllVarsAreInt;

	private OctagonState(final Map<Term, Integer> mapNumericVarToIndex, final OctMatrix numericAbstraction,
			final boolean allVarsAreInt) {
		mMapNumericVarToIndex = mapNumericVarToIndex;
		mNumericAbstraction = numericAbstraction;
		mAllVarsAreInt = allVarsAreInt;
	}

	/**
	 * Constructs a OctagonState from a given collection of conjuncts
	 */
	public static OctagonState from(final Term[] conjuncts, final Script script) {
		final List<OctagonRelation> octRelations = new ArrayList<>();
		final Map<Term, Integer> varToIndex = new HashMap<>();
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
			varToIndex.putIfAbsent(octRel.getVar1(), varToIndex.size());
			varToIndex.putIfAbsent(octRel.getVar2(), varToIndex.size());
		}
		boolean allVarsAreInt = true;
		final OctMatrix resultMatrix = new OctMatrix(varToIndex.size());
		resultMatrix.fill(OctValue.INFINITY);
		for (final OctagonRelation octRel : octRelations) {
			final boolean isRealSort = SmtSortUtils.isRealSort(octRel.getVar1().getSort());
			allVarsAreInt &= !isRealSort;
			processRelation(varToIndex, octRel, resultMatrix, isRealSort);
		}
		return new OctagonState(varToIndex, resultMatrix, allVarsAreInt);
	}

	private static void processRelation(final Map<Term, Integer> varToIndex, final OctagonRelation octRel,
			final OctMatrix matrix, final boolean isRealSort) {
		final Rational constant;
		final boolean var1Negated;
		final boolean var2Negated;
		final Rational oldConstant = octRel.getConstant();
		switch (octRel.getRelationSymbol()) {
		case LEQ:
			constant = octRel.getConstant();
			var1Negated = octRel.isNegateVar1();
			var2Negated = octRel.isNegateVar2();
			break;
		case GEQ:
			constant = octRel.getConstant().negate();
			var1Negated = !octRel.isNegateVar1();
			var2Negated = !octRel.isNegateVar2();
			break;
		case LESS:
			// For int sort: Replace a+b < c by a+b <= c-1
			// For real sort: Replace a+b < c by a+b <= c (overapproximation)
			constant = isRealSort ? oldConstant : oldConstant.sub(Rational.ONE);
			var1Negated = octRel.isNegateVar1();
			var2Negated = octRel.isNegateVar2();
			break;
		case GREATER:
			// For int sort: Replace a+b > c by -a-b <= -c-1
			// For real sort: Replace a+b > c by -a-b <= -c (overapproximation)
			constant = isRealSort ? oldConstant.negate() : oldConstant.negate().sub(Rational.ONE);
			var1Negated = !octRel.isNegateVar1();
			var2Negated = !octRel.isNegateVar2();
			break;
		default:
			return;
		}
		final BigDecimal constantAsDecimal =
				new BigDecimal(constant.numerator()).divide(new BigDecimal(constant.denominator()));
		// OctagonRelation and OctMatrix use different representations, therefore we need to negate var2Negated
		matrix.assumeVarRelationLeConstant(varToIndex.get(octRel.getVar1()), var1Negated,
				varToIndex.get(octRel.getVar2()), !var2Negated, new OctValue(constantAsDecimal));
	}

	private Term[] getIndexToTermArray() {
		final Term[] result = new Term[mMapNumericVarToIndex.size()];
		for (final Entry<Term, Integer> entry : mMapNumericVarToIndex.entrySet()) {
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
		return Arrays.toString(getIndexToTermArray()) + "\n" + mNumericAbstraction.toString();
	}

	private OctMatrix cachedSelectiveClosure() {
		return mAllVarsAreInt ? mNumericAbstraction.cachedTightClosure() : mNumericAbstraction.cachedStrongClosure();
	}

	private OctagonState applyMergeOperator(final OctagonState other, final BinaryOperator<OctMatrix> matrixOp) {
		final Map<Term, Integer> varToIndex = new HashMap<>();
		final Set<Term> allVars =
				DataStructureUtils.union(mMapNumericVarToIndex.keySet(), other.mMapNumericVarToIndex.keySet());
		final int[] copyInstructions1 = new int[allVars.size()];
		final int[] copyInstructions2 = new int[allVars.size()];
		int lastIndex = mMapNumericVarToIndex.size();
		boolean allVarsAreInt = mAllVarsAreInt;
		for (final Term variable : allVars) {
			final int index1 = mMapNumericVarToIndex.getOrDefault(variable, -1);
			final int index2 = other.mMapNumericVarToIndex.getOrDefault(variable, -1);
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
		final OctMatrix matrix1 = rearrangeIfNecessary(bestAvailableClosure(), copyInstructions1);
		final OctMatrix matrix2 = rearrangeIfNecessary(other.bestAvailableClosure(), copyInstructions2);
		return new OctagonState(varToIndex, matrixOp.apply(matrix1, matrix2), allVarsAreInt);
	}

	private static OctMatrix rearrangeIfNecessary(final OctMatrix matrix, final int[] copyInstructions) {
		for (int i = 0; i < copyInstructions.length; i++) {
			if (copyInstructions[i] != i) {
				return matrix.rearrange(copyInstructions);
			}
		}
		// The copyInstructions are simply the identity, so there is no need to rearrange
		return matrix;
	}

	private OctMatrix bestAvailableClosure() {
		if (mAllVarsAreInt && mNumericAbstraction.hasCachedTightClosure()) {
			return mNumericAbstraction.cachedTightClosure();
		} else if (mNumericAbstraction.hasCachedStrongClosure()) {
			return mNumericAbstraction.cachedStrongClosure();
		}
		return mNumericAbstraction;
	}

	@Override
	public OctagonState widen(final OctagonState other) {
		// TODO: Make the widening operator a setting?
		return applyMergeOperator(other, OctMatrix::widenSimple);
	}

	@Override
	public OctagonState join(final OctagonState other) {
		return applyMergeOperator(other, OctMatrix::max);
	}
}
