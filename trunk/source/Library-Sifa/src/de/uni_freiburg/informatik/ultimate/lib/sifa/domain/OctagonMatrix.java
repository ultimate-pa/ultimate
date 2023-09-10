/*
 * Copyright (C) 2015-2017 Claus Schätzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2023 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2023 University of Freiburg
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

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.BiPredicate;
import java.util.function.BinaryOperator;
import java.util.function.Consumer;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.OctagonRelation;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Matrix representation of octagons, based on A. Miné's "The octagon abstract domain"
 * (https://www-apr.lip6.fr/~mine/publi/article-mine-ast01.pdf).
 *
 * <p>
 * Octagons store constraints of the form <i>±vi ± vj ≤ c</i> over numerical variables <i>{v0, v1, ..., v(n-1)}</i>. An
 * octagon over <i>n</i> variables is a <i>2n×2n</i> matrix. Matrix indices are zero-based. Names and types of the
 * variables are not stored by the octagon. Each variable <i>vi</i> has two forms, a positive form <i>(+vi)</i> and a
 * negative form <i>(-vi)</i>. <i>vi+</i> corresponds to matrix row/colum <i>2i</i> and <i>vi-</i> corresponds to matrix
 * row/colum <i>2i+1</i>. Each matrix entry stores a constraint:
 * <table>
 * <thead>
 * <tr>
 * <th>Constraint</th>
 * <th>Corresponding matrix entry</th>
 * </tr>
 * <thead> <tbody>
 * <tr>
 * <td><i>(+vj) - (+vi) ≤ c</i></td>
 * <td><i>m(2i, 2j) = c<i></td>
 * </tr>
 * <tr>
 * <td><i>(+vj) - (-vi) ≤ c</i></td>
 * <td><i>m(2i+1, 2j) = c<i></td>
 * </tr>
 * <tr>
 * <td><i>(-vj) - (+vi) ≤ c</i></td>
 * <td><i>m(2i, 2j+1) = c<i></td>
 * </tr>
 * <tr>
 * <td><i>(-vj) - (-vi) ≤ c</i></td>
 * <td><i>m(2i+1, 2j+1) = c<i></td>
 * </tr>
 * </tbody>
 * </table>
 * Octagon matrices are divided into <i>2x2</i> blocks. Block row/column <i>i</i> contains the matrix rows/columns
 * <i>2i</i> and <i>2i+1</i>.
 *
 * <p>
 * The same constraint can be represented by in two ways: <i>(+vj)-(+vi)≤c ⇔ (-vi)-(-vj)≤c ⇔ m(2i,2j)=c ⇔
 * m(2j+1,2i+1)=c</i>. The following ASCII art shows matrix entries that effectively store the same constraints.
 *
 * <pre>
 *     \ .   D B   L J
 *     . \   C A   K I
 *
 *     A B   \ .   W Y
 *     C D   . \   Z X
 *
 *     I J   X Y   \ .
 *     K L   Z W   . \
 * </pre>
 *
 * An octagon matrix is coherent iff matrix entries that effectively represent the same constraint have the same values.
 * This class ensures coherence by storing only the block lower triangular matrix.
 *
 * <p>
 * Different octagons (matrices with different entries) may have the same concretization. Closures can be used as a
 * normal form for non-bottom octagons.
 *
 * @author Claus Schätzle (schaetzc@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class OctagonMatrix {

	public static final BiPredicate<Rational, Rational> sRelationEqual = (x, y) -> x.compareTo(y) == 0;
	public static final BiPredicate<Rational, Rational> sRelationLessThanOrEqual = (x, y) -> x.compareTo(y) <= 0;

	/**
	 * Empty octagon that stores constraints over the empty set of variables. Use {@link #NEW} and
	 * {@link #addVariables(int)} to create octagons of any size.
	 */
	public static final OctagonMatrix NEW = new OctagonMatrix(0);

	/**
	 * Used algorithm to compute the shortest path closure. All shortest path closure algorithms compute the same
	 * result, but may vary in terms of speed. The runtime of some algorithms depends on the content of the matrix.
	 */
	private static final Consumer<OctagonMatrix> sDefaultShortestPathClosure =
			OctagonMatrix::shortestPathClosurePrimitiveSparse;

	/**
	 * Size of this matrix (size = #rows = #columns). Size is always an even number.
	 *
	 * @see #variables()
	 */
	private final int mSize;

	/**
	 * Stores the entries (= elements) of this matrix.
	 * <p>
	 * Some entries are neglected because they are coherent to other entries (see documentation of this class). The
	 * stored entries and their indices are shown in the following ASCII art.
	 *
	 * <pre>
	 *     0 1 . . . .    legend
	 *     2 3 . . . .    -----------------
	 *     4 5 6 7 . .    .      not stored
	 *     8 9 # # . .    0-9 #  stored
	 *     # # # # # #
	 *     # # # # # #    m_0,0 is top left
	 * </pre>
	 *
	 * The matrix is divided into 2x2 blocks. Every block that contains at least one element from the block lower
	 * triangular matrix is completely stored. Entries are stored row-wise from top to bottom, left to right.
	 *
	 * @see #indexOf(int, int)
	 */
	private final Rational[] mEntries;

	/**
	 * Cached strong closure of this matrix. {@code null} if cache is empty. This cache has to be updated, if this
	 * matrix changes.
	 */
	private OctagonMatrix mStrongClosure;

	/**
	 * Cached tight closure of this matrix. {@code null} if cache is empty. This cache has to be updated, if this matrix
	 * changes.
	 */
	private OctagonMatrix mTightClosure;

	/**
	 * Creates a copy of this matrix. The copy can be used like a deep copy. Only the cached closures are shallow
	 * copies.
	 *
	 * @return Copy of this matrix
	 */
	private OctagonMatrix copy() {
		final OctagonMatrix copy = new OctagonMatrix(variables());
		System.arraycopy(mEntries, 0, copy.mEntries, 0, mEntries.length);
		copy.mStrongClosure = (mStrongClosure == this) ? copy : mStrongClosure;
		copy.mTightClosure = (mTightClosure == this) ? copy : mTightClosure;
		return copy;
	}

	/**
	 * Creates a new matrix of the given size. Initially, the matrix entries are {@code null}.
	 *
	 * @param variables
	 *            Number of variables (= 2 * #rows = 2 * #columns) of the matrix
	 */
	public OctagonMatrix(final int variables) {
		mSize = variables * 2;
		mEntries = new Rational[entriesInBlockLowerTriangular(variables)];
		fill(Rational.POSITIVE_INFINITY);
	}

	private static int entriesInBlockLowerTriangular(final int variables) {
		return 2 * (variables * variables + variables);
	}

	/**
	 * Fill this matrix with a given value.
	 *
	 * @param fill
	 *            Value to be used for all entries
	 */
	private void fill(final Rational fill) {
		for (int i = 0; i < mEntries.length; ++i) {
			mEntries[i] = fill;
		}
		mStrongClosure = mTightClosure = null;
	}

	/**
	 * Returns the number of rows (= number of columns) in this octagon matrix. Octagon matrices always have an
	 * even-numbered size, since every variable corresponds to two rows (and two columns) of the octagon matrix.
	 *
	 * @return size of this octagon matrix.
	 */
	public int getSize() {
		return mSize;
	}

	/**
	 * Returns the number of variables, stored by this octagon. Each variable corresponds to two rows and two columns of
	 * the octagon matrix.
	 *
	 * @return number of variables in this octagon
	 */
	public int variables() {
		return mSize / 2;
	}

	/**
	 * Reads an entry of this matrix. This method can also read entries from the block upper triangular matrix (which is
	 * not explicitly stored).
	 *
	 * @param row
	 *            Matrix row (zero-based)
	 * @param col
	 *            Matrix column (zero-based)
	 * @return Matrix entry in the given row and column
	 */
	private Rational get(final int row, final int col) {
		return mEntries[indexOf(row, col)];
	}

	/**
	 * Writes an entry of this matrix. This method can also write entries of the block upper triangular matrix (which is
	 * not explicitly stored). Coherence is assured, which means that writing one entry also changes the coherent entry.
	 *
	 * @param row
	 *            Matrix row (zero-based)
	 * @param col
	 *            Matrix column (zero-based)
	 * @return Matrix entry in the given row and column
	 */
	private void set(final int row, final int col, final Rational value) {
		assert value != null : "null is not a valid matrix entry.";
		mStrongClosure = mTightClosure = null;
		mEntries[indexOf(row, col)] = value;
	}

	/**
	 * Changes an entry of this matrix iff the new value is smaller than the old value. If the new value is not smaller
	 * than the old value, this matrix remains unchanged.
	 * <p>
	 * This method models the effect of {@code assume vCol - vRow <= newValue}, where {@code vRow} and {@code vCol} are
	 * positive or negative forms of a program variable.
	 *
	 * @param row
	 *            Row of the matrix entry
	 * @param col
	 *            Column of the matrix entry
	 * @param newValue
	 *            New value of the matrix entry (must be smaller than the old value to have an effect)
	 */
	private void setMin(final int row, final int col, final Rational newValue) {
		assert newValue != null : "null is not a valid matrix entry.";
		final int index = indexOf(row, col);
		if (newValue.compareTo(mEntries[index]) < 0) {
			mEntries[index] = newValue;
			mStrongClosure = mTightClosure = null;
		}
	}

	public void processRelation(final OctagonRelation octRel, final Map<Term, Integer> varToIndex) {
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
			constant =
					SmtSortUtils.isRealSort(octRel.getVar1().getSort()) ? oldConstant : oldConstant.sub(Rational.ONE);
			var1Negated = octRel.isNegateVar1();
			var2Negated = octRel.isNegateVar2();
			break;
		case GREATER:
			// For int sort: Replace a+b > c by -a-b <= -c-1
			// For real sort: Replace a+b > c by -a-b <= -c (overapproximation)
			constant = SmtSortUtils.isRealSort(octRel.getVar1().getSort()) ? oldConstant.negate()
					: oldConstant.negate().sub(Rational.ONE);
			var1Negated = !octRel.isNegateVar1();
			var2Negated = !octRel.isNegateVar2();
			break;
		default:
			return;
		}
		int var1 = 2 * varToIndex.get(octRel.getVar1());
		int var2 = 2 * varToIndex.get(octRel.getVar2());
		if (!var1Negated) {
			// negative form of var1
			var1 = var1 | 0b1;
		}
		if (!var2Negated) {
			// negative form of var2
			var2 = var2 | 0b1;
		}
		setMin(var1, var2, constant);
	}

	/**
	 * Sets positive values on the main diagonal to zero. Negative values are kept, since they denote that this octagon
	 * is \bot. When encountering a negative value, this method exits early => positive values may remain on the
	 * diagonal.
	 *
	 * @return A value on the main diagonal was smaller than zero (=> negative self loop => this=\bot)
	 */
	private boolean minimizeDiagonal() {
		for (int i = 0; i < mSize; ++i) {
			if (minimizeDiagonalEntry(i)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Updates a diagonal entry {@code x} with {@code min(x,0)}.
	 *
	 * @param rowCol
	 *            Row (= column) of the diagonal entry
	 * @return The diagonal entry was negative.
	 */
	private boolean minimizeDiagonalEntry(final int rowCol) {
		final int idx = indexOfLower(rowCol, rowCol);
		final int sig = mEntries[idx].signum();
		if (sig > 0) {
			mEntries[idx] = Rational.ZERO;
			// no need to reset cached closures
			// diagonal is always minimized on closure computation
			return false;
		}
		return sig < 0;
	}

	/**
	 * Computes the index of any matrix entry for the array {@link #mEntries}. Coherent matrix entries have the same
	 * index.
	 *
	 * @param row
	 *            Matrix row
	 * @param col
	 *            Matrix column
	 * @return Index (for {@link #mEntries}) of the given matrix entry
	 */
	private int indexOf(final int row, final int col) {
		assert row < mSize && col < mSize : row + "," + col + " is not an index for matrix of size " + mSize + ".";
		if (row < col) {
			return indexOfLower(col ^ 1, row ^ 1);
		}
		return indexOfLower(row, col);
	}

	/**
	 * Computes the index of an block lower triangular matrix entry for the array {@link #mEntries}. This method only
	 * works for entries of the block lower triangular matrix!
	 *
	 * @param row
	 *            Matrix row
	 * @param col
	 *            Matrix column
	 * @return Index (for {@link #mEntries}) of the given matrix entry
	 *
	 * @see #indexOf(int, int)
	 */
	private static int indexOfLower(final int row, final int col) {
		return col + (row + 1) * (row + 1) / 2;
	}

	/**
	 * Performs a binary element-wise (= point-wise) operation on matrices. {@code this} is the first operand and
	 * {@code other} is the second operand. Both operands remain unchanged.
	 *
	 * @param other
	 *            Second operand
	 * @param operator
	 *            Operation to be performed for each pair of entries
	 * @return Result of the operation
	 */
	private OctagonMatrix elementwiseOperation(final OctagonMatrix other, final BinaryOperator<Rational> operator) {
		checkCompatibility(other);
		final OctagonMatrix result = new OctagonMatrix(variables());
		for (int i = 0; i < mEntries.length; ++i) {
			result.mEntries[i] = operator.apply(mEntries[i], other.mEntries[i]);
		}
		return result;
	}

	/**
	 * Checks a binary element-wise (= point-wise) relation on matrices. {@code this} is the left hand side and
	 * {@code other} is the right hand side of the relation. Both sides remain unchanged.
	 *
	 * @param other
	 *            Right hand side of the relation
	 * @param relation
	 *            Elementwise relation to be checked
	 * @return All pairs of corresponding entries were in the relation
	 */
	private boolean elementwiseRelation(final OctagonMatrix other, final BiPredicate<Rational, Rational> relation) {
		checkCompatibility(other);
		for (int i = 0; i < mEntries.length; ++i) {
			if (!relation.test(mEntries[i], other.mEntries[i])) {
				return false;
			}
		}
		return true;
	}

	private boolean elementwiseRelation(final OctagonMatrix other, final BiPredicate<Rational, Rational> relation,
			final int[] mapThisVarIndexToPermVarIndex) {
		if (mapThisVarIndexToPermVarIndex == null) {
			return elementwiseRelation(other, relation);
		}
		checkCompatibility(other);
		for (int bRow = 0; bRow < variables(); ++bRow) {
			// compare only block lower triangular part (upper part is coherent)
			for (int bCol = 0; bCol <= bRow; ++bCol) {
				final int permBRow = mapThisVarIndexToPermVarIndex[bRow];
				final int permBCol = mapThisVarIndexToPermVarIndex[bCol];
				if (!blockwiseRelation(bRow, bCol, other, permBRow, permBCol, relation)) {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * Checks whether a 2×2 block of this matrix is in an elementwise relation to another 2×2 block of (possibly
	 * another) matrix. Block row/column with index <i>i</i> contains the rows/columns <i>2i</i> and <i>2i+1</i>.
	 *
	 * @param bRow
	 *            Block row index in this matrix
	 * @param bCol
	 *            Block column index in this matrix
	 * @param other
	 *            Other matrix
	 * @param otherBRow
	 *            Block row index in other matrix
	 * @param otherBCol
	 *            Block column index in the other matrix
	 * @param relation
	 *            Elementwise Relation to be checked
	 * @return All pairs of corresponding entries from the specified blocks were in the relation
	 */
	private boolean blockwiseRelation(int bRow, int bCol, final OctagonMatrix other, int otherBRow, int otherBCol,
			final BiPredicate<Rational, Rational> relation) {
		bRow *= 2;
		bCol *= 2;
		otherBRow *= 2;
		otherBCol *= 2;
		for (int j = 0; j < 2; ++j) {
			for (int i = 0; i < 2; ++i) {
				if (!relation.test(get(bRow + i, bCol + j), other.get(otherBRow + i, otherBCol + j))) {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * Checks whether this and another matrix are compatible for a element-wise operation or relation. An exception is
	 * thrown for incompatible matrices. Matrixes are compatible if they have the same size.
	 *
	 * @param other
	 *            Other octagon
	 * @throws IllegalArgumentException
	 *             The matrices are incompatible
	 */
	private void checkCompatibility(final OctagonMatrix other) {
		if (other.mSize != mSize) {
			throw new IllegalArgumentException("Incompatible matrices");
		}
	}

	/**
	 * Create a rearranged version of this matrix. Variables can be swapped, added, or removed.
	 *
	 * @param mapNewToOldVar
	 *            Array of length {@code n}, where {@code n} is the number of variables inside the rearranged matrix.
	 *            For variable {@code i} of the rearranged matrix, {@code mapNewToOldVar[i]} is the variable of the
	 *            source (this) matrix or a negative number if {@code i} is a fresh variable.
	 *
	 * @return Rearranged matrix.
	 *
	 * @see #copySelection(OctagonMatrix, Map)
	 */
	public OctagonMatrix rearrange(final int[] mapNewToOldVar) {
		final OctagonMatrix n = new OctagonMatrix(mapNewToOldVar.length);

		final Map<Integer, Integer> copyTargetFromSourceVar = new HashMap<>();
		int unchangedPrefixVars = 0;
		int freshSuffixVars = 0;
		for (int newVar = 0; newVar < mapNewToOldVar.length; ++newVar) {
			final int oldVar = mapNewToOldVar[newVar];
			final boolean addNewVar = oldVar < 0;
			copyTargetFromSourceVar.put(newVar, addNewVar ? null : oldVar);
			if (newVar == oldVar && unchangedPrefixVars == newVar) {
				++unchangedPrefixVars;
			}
			if (addNewVar) {
				++freshSuffixVars;
			} else {
				freshSuffixVars = 0;
			}
		}
		final int freshSuffixStartVar = n.variables() - freshSuffixVars;
		final int unchangedPrefixEntries = entriesInBlockLowerTriangular(unchangedPrefixVars);
		System.arraycopy(mEntries, 0, n.mEntries, 0, unchangedPrefixEntries);
		n.copySelection(this, copyTargetFromSourceVar, unchangedPrefixVars, freshSuffixStartVar);
		final int freshSuffixStart = entriesInBlockLowerTriangular(freshSuffixStartVar);
		Arrays.fill(n.mEntries, freshSuffixStart, n.mEntries.length, Rational.POSITIVE_INFINITY);
		return n;
	}

	private static Rational min(final Rational r1, final Rational r2) {
		return r1.compareTo(r2) < 0 ? r1 : r2;
	}

	private static Rational max(final Rational r1, final Rational r2) {
		return r1.compareTo(r2) > 0 ? r1 : r2;
	}

	/**
	 * Computes the element-wise minimum of two matrices with the same size. The element-wise minimum is a meet operator
	 * for octagons (over-approximates the intersection of octagons).
	 *
	 * @param m
	 *            First matrix
	 * @param n
	 *            Second matrix
	 * @return Element-wise minimum
	 */
	public static OctagonMatrix min(final OctagonMatrix m, final OctagonMatrix n) {
		return m.elementwiseOperation(n, OctagonMatrix::min);
	}

	/**
	 * Computes the element-wise maximum of two matrices with the same size. The element-wise maximum is a join operator
	 * for octagons (over-approximates the union of octagons).
	 *
	 * @param m
	 *            First matrix
	 * @param n
	 *            Second matrix
	 * @return Element-wise minimum
	 */
	public static OctagonMatrix max(final OctagonMatrix m, final OctagonMatrix n) {
		final OctagonMatrix result = m.elementwiseOperation(n, OctagonMatrix::max);
		// a and b are closed ==> max(a,b) is closed
		if (m.mStrongClosure != null && n.mStrongClosure != null) {
			result.mStrongClosure = result;
		}
		if (m.mTightClosure != null && n.mTightClosure != null) {
			result.mTightClosure = result;
		}
		return result;
	}

	/**
	 * Checks whether this and another matrix of the same size are equal, that is, if both have the same entries.
	 * Different octagon matrices may have the same concretization! Closures can be used as a normal form for non-bottom
	 * octagons.
	 *
	 * @param other
	 *            Other matrix
	 * @return The matrices are equal
	 */
	public boolean isEqualTo(final OctagonMatrix other) {
		if (this == other) {
			return true;
		}
		return elementwiseRelation(other, sRelationEqual);
	}

	/**
	 * Checks whether this and another octagon matrix of the same size are equal, considering that the order of
	 * variables was permuted in the other matrix.
	 * <p>
	 * The permutation must be known. If this octagon matrix uses the variable order <code>{v0, v1, v2}</code> and the
	 * other octagon matrix uses the variable order <code>{v1, v2, v0}</code>, then the permutation is
	 * <code>[2, 0, 1]</code>.
	 * <p>
	 * Different octagon matrices may have the same concretization! Closures can be used as a normal form for non-bottom
	 * octagons.
	 *
	 *
	 * @param permutation
	 *            Other matrix (possibly a permutation of this matrix)
	 * @param mapThisVarIndexToPermVarIndex
	 *            Map from variable indices (array index) of this octagon matrix to the corresponding variable indices
	 *            (array entries) of the permuted octagon matrix. {@code null} for non-permuted matrices.
	 * @return The matrices are equal
	 */
	public boolean isEqualTo(final OctagonMatrix permutation, final int[] mapThisVarIndexToPermVarIndex) {
		return elementwiseRelation(permutation, sRelationEqual, mapThisVarIndexToPermVarIndex);
	}

	/**
	 * Returns the strong closure of this octagon matrix. The strong closure is only computed, if it is not already
	 * cached. The original cache is returned. Do not modify!
	 *
	 * @return Strong closure
	 */
	public OctagonMatrix cachedStrongClosure() {
		if (mStrongClosure != null) {
			return mStrongClosure;
		}
		return strongClosure(sDefaultShortestPathClosure);
	}

	/**
	 * @return The strong closure of this matrix was already computed and cached
	 */
	public boolean hasCachedStrongClosure() {
		return mStrongClosure != null;
	}

	/**
	 * Computes the strong closure of this octagon matrix. The strong closure is a normal form for non-bottom octagon
	 * matrices over real-valued variables.
	 *
	 * @param shortestPathClosureAlgorithm
	 *            Algorithm to be used for the computation of the shortest path closure
	 * @return Strong closure
	 */
	private OctagonMatrix strongClosure(final Consumer<OctagonMatrix> shortestPathClosureAlgorithm) {
		final OctagonMatrix strongClosure = copy();
		final boolean obviouslyBottom = strongClosure.minimizeDiagonal();
		if (!obviouslyBottom) {
			shortestPathClosureAlgorithm.accept(strongClosure);
			strongClosure.strengtheningInPlace();
		}
		strongClosure.mStrongClosure = mStrongClosure = strongClosure;
		strongClosure.mTightClosure = mTightClosure;
		return strongClosure;
	}

	/**
	 * Returns the tight closure of this octagon matrix. The tight closure is only computed, if it is not already
	 * cached. The original cache is returned. Do not modify!
	 *
	 * @return Tight closure
	 */
	public OctagonMatrix cachedTightClosure() {
		if (mTightClosure != null) {
			return mTightClosure;
		}
		return tightClosure(sDefaultShortestPathClosure);
	}

	/**
	 * @return The tight closure of this matrix was already computed and cached
	 */
	public boolean hasCachedTightClosure() {
		return mTightClosure != null;
	}

	/**
	 * Computes the tight closure of this octagon matrix. The tight closure is a normal form for non-bottom octagon
	 * matrices over integer variables.
	 *
	 * @param shortestPathClosureAlgorithm
	 *            Algorithm to be used for the computation of the shortest path closure
	 * @return Tight closure
	 */
	private OctagonMatrix tightClosure(final Consumer<OctagonMatrix> shortestPathClosureAlgorithm) {
		final OctagonMatrix tightClosure;
		tightClosure = copy();
		if (!tightClosure.minimizeDiagonal()) {
			// this matrix is obviously bottom
			shortestPathClosureAlgorithm.accept(tightClosure);
			// cached strong closure is not re-used
			// because strong closure is unlikely to be in cache when tight
			// closure is needed
			tightClosure.tighteningInPlace();
		}
		tightClosure.mStrongClosure = mStrongClosure;
		tightClosure.mTightClosure = mTightClosure = tightClosure;
		return tightClosure;
	}

	/**
	 * Computes the shortest path closure in-place, as in {@link #shortestPathClosureSparse()}, while using only one
	 * primitive array instead of two java collections to represent the index.
	 */
	public void shortestPathClosurePrimitiveSparse() {
		// indices of finite entries in rows k and k^1
		int[] rk = null;
		// indices of finite entries in columns k and k^1
		int[] ck = null;
		int indexLength = 0;
		for (int k = 0; k < mSize; ++k) {
			final int kk = k ^ 1;
			if (k < kk) {
				// k is even => entered new 2x2 block
				rk = new int[mSize];
				ck = new int[mSize];
				indexLength = primitiveIndexFiniteEntriesInBlockRowAndColumn(k, rk, ck);
			}
			for (int _i = 0; _i < indexLength; ++_i) {
				final int i = ck[_i];
				final Rational ik = get(i, k);
				final Rational ikk = get(i, kk);
				final int maxCol = i | 1;
				for (int _j = 0; _j < indexLength; ++_j) {
					final int j = rk[_j];
					if (j > maxCol) {
						break;
					}
					final Rational kj = get(k, j);
					final Rational kkj = get(kk, j);
					final Rational indirectRoute = min(ik.add(kj), ikk.add(kkj));
					if (get(i, j).compareTo(indirectRoute) > 0) {
						set(i, j, indirectRoute);
					}
				}
			}
		}
	}

	/**
	 * Indexes the the finite entries in block row k/2 and a block column k/2 at the same time. If the computed row
	 * index contains the value i, then there is a finite matrix entry at matrix index (i,k) or (i,k+1). If the computed
	 * column index contains the value i, then there is a finite matrix entry at matrix index (k,i), or (k+1,i).
	 * <p>
	 * The returned array has always the length {@link #getSize()}, but only the first n index entries are used. The
	 * length n of the index is the return value of this method. The row and column index always have the same length.
	 *
	 * @param k
	 *            First row/column index of the block row/column (always an even number)
	 * @param rowIndex
	 *            Index of finite entries in block row k/2 (outgoing edges of k and k+1). This index is not completely
	 *            sorted! The values 2i and 2i+1 are swapped.
	 * @param colIndex
	 *            Index of finite entries in block column k/2 (incoming edges of k and k+1)
	 * @return Actual length of the row/column index
	 */
	private int primitiveIndexFiniteEntriesInBlockRowAndColumn(final int k, final int[] rowIndex,
			final int[] colIndex) {
		int indexLength = 0;
		final int kk = k ^ 1;
		for (int i = 0; i < mSize; ++i) {
			if (!get(i, k).equals(Rational.POSITIVE_INFINITY) || !get(i, kk).equals(Rational.POSITIVE_INFINITY)) {
				colIndex[indexLength] = i;
				rowIndex[indexLength] = i ^ 1;
				++indexLength;
			}
		}
		return indexLength;
	}

	/**
	 * Computes the strong closure from this matrix in-place, as presented by Bagnara, Hill, and Zaffanella
	 * (https://arxiv.org/pdf/0705.4618v2).
	 * <p>
	 * This matrix has to be in shortest-path-closure form.
	 */
	private void strengtheningInPlace() {
		// blocks on the diagonal (upper, lower bounds) won't change by
		// strengthening
		// => iterate only 2x2 blocks that are _strictly_ below the main
		// diagonal
		for (int i = 2; i < mSize; ++i) {
			final Rational ib = get(i, i ^ 1).div(Rational.TWO);
			final int maxCol = (i - 2) | 1;
			for (int j = 0; j <= maxCol; ++j) {
				final Rational jb = get(j ^ 1, j).div(Rational.TWO);
				final Rational b = ib.add(jb);
				if (get(i, j).compareTo(b) > 0) {
					set(i, j, b);
				}
			}
		}
	}

	/**
	 * Computes the tight closure of this matrix in-place, as presented by Bagnara, Hill, and Zaffanella
	 * (https://arxiv.org/pdf/0705.4618v2).
	 * <p>
	 * This matrix has to be in shortest-path-closure form.
	 */
	private void tighteningInPlace() {
		for (int i = 0; i < mSize; ++i) {
			final Rational ib = get(i, i ^ 1).div(Rational.TWO).floor();
			final int maxCol = i | 1;
			for (int j = 0; j <= maxCol; ++j) {
				final Rational jb = get(j ^ 1, j).div(Rational.TWO).floor();
				final Rational b = ib.add(jb);
				if (get(i, j).compareTo(b) > 0) {
					set(i, j, b);
				}
			}
		}
	}

	/**
	 * Checks for negative self loops in the graph represented by this adjacency matrix. Self loops are represented by
	 * this matrix' diagonal entries.
	 * <p>
	 * <b>m</b> is strongly closed and has a negative self loop <=> <b>m</b> is empty in <b>R</b><br>
	 * <b>m</b> is tightly closed and has a negative self loop <=> <b>m</b> is empty in <b>Z</b>
	 *
	 * @return a negative self loop exists
	 */
	public boolean hasNegativeSelfLoop() {
		for (int i = 0; i < mSize; ++i) {
			if (get(i, i).signum() < 0) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Widens this octagon by another one. Constraints that would be loosened by a normal join are immediately removed
	 * by this widening operator.
	 * <p>
	 * This widening operator was presented by Mine (http://www-apr.lip6.fr/~mine/publi/article-mine-ast01.pdf).
	 *
	 * @param n
	 *            Other octagon
	 * @return This octagon, widened with {@code n}
	 */
	public OctagonMatrix widenSimple(final OctagonMatrix n) {
		return elementwiseOperation(n, (mij, nij) -> mij.compareTo(nij) >= 0 ? mij : Rational.POSITIVE_INFINITY);
	}

	/**
	 * Widens this octagon by another one. Constraints that would be loosened by a normal join are loosened even more,
	 * using a binary exponential backoff. Constraints are removed, once the backoff reaches a given threshold. The
	 * threshold has to be finite to ensure stabilization of this widening operator.
	 *
	 * @param n
	 *            Other octagon
	 * @param threshold
	 *            Finite threshold (updated matrix entries > threshold will be set to infinity)
	 * @return This octagon, widened with {@code n}
	 */
	public OctagonMatrix widenExponential(final OctagonMatrix n, final Rational threshold) {
		final Rational epsilon = Rational.ONE;
		final Rational minusTwoEpsilon = epsilon.add(epsilon).negate();
		final Rational oneHalfEpsilon = epsilon.div(Rational.TWO);
		return elementwiseOperation(n, (mij, nij) -> {
			if (mij.compareTo(nij) >= 0) {
				return mij;
			} else if (nij.compareTo(threshold) > 0) {
				return Rational.POSITIVE_INFINITY;
			}
			Rational result;
			if (nij.compareTo(minusTwoEpsilon) <= 0) {
				// there is no -inf => will always converge
				result = nij.div(Rational.TWO);
				// towards 0
			} else if (nij.signum() <= 0) {
				result = Rational.ZERO;
			} else if (nij.compareTo(oneHalfEpsilon) <= 0) {
				result = epsilon;
			} else {
				// 2 * nij
				result = nij.add(nij);
			}
			return min(result, threshold);
		});
	}

	/**
	 * Used for {@link OctagonMatrix#widenStepwise(OctagonMatrix, WideningStepSupplier)}.
	 *
	 * @author schaetzc@informatik.uni-freiburg.de
	 */
	public interface WideningStepSupplier {

		/**
		 * Returns a value used for widening. The widened value must be greater than or equal to the old value. The
		 * value infinity must be reached in an infinite number of steps for the widening operator to stabilize.
		 *
		 * @param val
		 *            Matrix entry which was increased by join and should be widened.
		 * @return Value greater than or equal to {@code val}
		 */
		Rational nextWideningStep(final Rational val);
	}

	/**
	 * Widens this octagon by another one. Constraints that would be loosened by a normal join are loosened even more,
	 * using a {@link WideningStepSupplier} to look up the next looser constraint. Usually, the widening steps are the
	 * literals from the analyzed program.
	 *
	 * @param n
	 *            Other octagon
	 * @param stepSupplier
	 *            Widening step supplier
	 * @return This octagon, widened with {@code n}
	 */
	public OctagonMatrix widenStepwise(final OctagonMatrix n, final WideningStepSupplier stepSupplier) {
		return elementwiseOperation(n, (mij, nij) -> {
			if (mij.compareTo(nij) >= 0) {
				return mij;
			}
			return stepSupplier.nextWideningStep(nij);
		});
	}

	/**
	 * Copies selected block rows/columns of any matrix to this matrix. The matrices can be of different size. The
	 * source and target (this) matrix have to be different objects.
	 * <p>
	 * This method can also be used to permute the order of variables (that is, the order of block/rows columns). The
	 * following ASCII art shows what this method does. Each symbol from <code>· A B C D | -- ∞</code> depicts a 2x2
	 * block. The ∞-blocks are filled with {@link Rational#INFINITY}.
	 *
	 * <pre>
	 * target (this)     source           result
	 *                       x y            y   x
	 * · · · · · ·       · · | | ·        · ∞ · ∞ · ·
	 * · · · · · ·       · · | | ·        · ∞ · ∞ · ·
	 * · · · · · ·     x ----A-B--      y ∞ D ∞ C ∞ ∞
	 * · · · · · ·     y ----C-D--        · ∞ · ∞ · ·
	 * · · · · · ·       · · | | ·      x ∞ B ∞ A ∞ ∞
	 * · · · · · ·                        · ∞ · ∞ · ·
	 *   1 ------------------> 3
	 *       3 ------------> 2
	 *   mapTargetVarToSourceVar
	 * </pre>
	 *
	 * Computing the closure in advance, can reduce information loss.
	 *
	 * @param source
	 *            Matrix to copy values from. Must be a different object than this matrix.
	 * @param mapTargetToSourceVar
	 *            Indices of block rows/columns to be copied. The keys are indices in the target (this) matrix. The
	 *            values are indices in the source (a different!) matrix. Values may be {@code null} for new variables.
	 *            Keys must not be {@code null}.
	 */
	public void copySelection(final OctagonMatrix source, final Map<Integer, Integer> mapTargetToSourceVar,
			int skipVarsLessThan, int skipVarsBiggerEqualThan) {

		skipVarsLessThan = Math.min(0, skipVarsLessThan);
		skipVarsBiggerEqualThan = Math.min(variables(), skipVarsBiggerEqualThan);

		assert !containsTautology(source, mapTargetToSourceVar, skipVarsLessThan,
				skipVarsBiggerEqualThan) : "Overwrite in place with same target and source is not necessary and may cause problems.";

		for (final Map.Entry<Integer, Integer> entry : mapTargetToSourceVar.entrySet()) {
			final int targetVar = entry.getKey();
			if (targetVar < skipVarsLessThan || skipVarsBiggerEqualThan <= targetVar) {
				continue;
			}
			final Integer sourceVar = entry.getValue();
			// Copy columns. Rows are copied by coherence.
			for (int targetOther = skipVarsLessThan; targetOther < skipVarsBiggerEqualThan; ++targetOther) {
				if (targetOther < targetVar && mapTargetToSourceVar.containsKey(targetOther)) {
					// coherent block was already copied
					continue;
				}
				final Integer sourceOther = mapTargetToSourceVar.get(targetOther);
				if (sourceOther == null || sourceVar == null) {
					setBlock(targetOther, targetVar, Rational.POSITIVE_INFINITY);
				} else {
					copyBlock(targetOther, targetVar, /* := */ source, sourceOther, sourceVar);
				}
			}
		}
	}

	private boolean containsTautology(final OctagonMatrix source, final Map<Integer, Integer> mapTargetToSourceVar,
			final int skipVarsLessThan, final int skipVarsBiggerEqualThan) {
		return source.mEntries == mEntries
				&& mapTargetToSourceVar.entrySet().stream().anyMatch(entry -> skipVarsLessThan <= entry.getKey()
						&& entry.getKey() < skipVarsBiggerEqualThan && entry.getKey().equals(entry.getValue()));
	}

	private void copyBlock(int targetBRow, int targetBCol, final OctagonMatrix source, int sourceBRow, int sourceBCol) {
		targetBRow *= 2;
		targetBCol *= 2;
		sourceBRow *= 2;
		sourceBCol *= 2;
		for (int col = 0; col < 2; ++col) {
			for (int row = 0; row < 2; ++row) {
				set(targetBRow + row, targetBCol + col, source.get(sourceBRow + row, sourceBCol + col));
			}
		}
	}

	private void setBlock(int bRow, int bCol, final Rational v) {
		bRow *= 2;
		bCol *= 2;
		for (int col = 0; col < 2; ++col) {
			for (int row = 0; row < 2; ++row) {
				set(bRow + row, bCol + col, v);
			}
		}
	}

	public Term getTerm(final Script script, final Term[] vars) {
		final Set<Term> rtr = new HashSet<>();
		for (int row = 0; row < 2 * variables(); ++row) {
			final Term rowVar = selectVar(script, row, vars);
			// iterate only block lower triangular matrix (skip coherent upper part)
			for (int col = 0; col < (row / 2 + 1) * 2; ++col) {
				final Rational entry = get(row, col);
				if (col == row) {
					if (entry.signum() < 0) {
						// constraint of the form (0 <= -1)
						return script.term("false");
					}
					// constraint of the form (0 <= 1)
					continue;
				}
				if (entry.equals(Rational.POSITIVE_INFINITY)) {
					continue;
				}
				final Term colVar = selectVar(script, col, vars);
				final Rational dualEntry = get(getDualIndex(row), getDualIndex(col));
				rtr.add(createBoundedDiffTerm(script, colVar, rowVar, entry, entry.negate().equals(dualEntry)));
			}
		}
		return SmtUtils.and(script, rtr);
	}

	private static int getDualIndex(final int index) {
		return index % 2 == 0 ? (index + 1) : (index - 1);
	}

	// returns variable in positive or negative form, depending on row or column
	private static Term selectVar(final Script script, final int rowCol, final Term[] vars) {
		final Term posNegVar = vars[rowCol / 2];
		if (rowCol % 2 == 1) {
			return script.term("-", posNegVar);
		}
		return posNegVar;
	}

	// returns minuend - subtrahend <= bound or minuend - subtrahend = bound (depending on isEquality)
	private static Term createBoundedDiffTerm(final Script script, Term minuend, Term subtrahend, final Rational bound,
			final boolean isEquality) {
		final Term tBound;
		final Term t = minuend;
		final boolean minuendIsInt = SmtSortUtils.isIntSort(t.getSort());
		final Term t1 = subtrahend;
		final boolean subtrahendIsInt = SmtSortUtils.isIntSort(t1.getSort());
		if (minuendIsInt && subtrahendIsInt) {
			tBound = bound.floor().toTerm(t.getSort());
		} else {
			tBound = bound.toTerm(SmtSortUtils.getRealSort(script));
			if (minuendIsInt) {
				minuend = script.term("to_real", minuend);
			} else if (subtrahendIsInt) {
				subtrahend = script.term("to_real", subtrahend);
			}
		}
		final Term diff = SmtUtils.minus(script, minuend, subtrahend);
		if (isEquality) {
			return SmtUtils.binaryEquality(script, diff, tBound);
		}
		return SmtUtils.leq(script, diff, tBound);
	}

	@Override
	public String toString() {
		return toStringHalf();
	}

	/**
	 * @return Multi-line string representation of this matrix (including the coherent, block upper triangular part)
	 */
	public String toStringFull() {
		final StringBuilder sb = new StringBuilder();
		for (int row = 0; row < mSize; ++row) {
			String delimiter = "";
			for (int col = 0; col < mSize; ++col) {
				sb.append(delimiter);
				sb.append(get(row, col));
				delimiter = "\t";
			}
			sb.append("\n");
		}
		return sb.toString();
	}

	/**
	 * @return Multi-line string representation of this block lower triangular matrix
	 */
	public String toStringHalf() {
		final StringBuilder sb = new StringBuilder();
		// input of integer sequence floor(n^2 / 2 -1)
		int n = 2;
		// index of last entry in current row (= output of integer sequence)
		int rowEnd = 1;
		for (int i = 0; i < mEntries.length; ++i) {
			sb.append(mEntries[i]);
			if (i == rowEnd) {
				sb.append("\n");
				++n;
				rowEnd = n * n / 2 - 1;
			} else {
				sb.append("\t");
			}
		}
		return sb.toString();
	}
}
