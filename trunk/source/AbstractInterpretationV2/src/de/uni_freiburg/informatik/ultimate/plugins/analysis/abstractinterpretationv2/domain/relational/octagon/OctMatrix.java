/*
 * Copyright (C) 2015-2017 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.MathContext;
import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ThreadLocalRandom;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.Consumer;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;

/**
 * Matrix representation of octagons, based on A. Miné's "The octagon abstract
 * domain" (https://www-apr.lip6.fr/~mine/publi/article-mine-ast01.pdf).
 *
 * <p>
 * Octagons store constraints of the form <i>±vi ± vj ≤ c</i> over numerical
 * variables <i>{v0, v1, ..., v(n-1)}</i>. An octagon over <i>n</i> variables is
 * a <i>2n×2n</i> matrix. Matrix indices are zero-based. Names and types of the
 * variables are not stored by the octagon. Each variable <i>vi</i> has two
 * forms, a positive form <i>(+vi)</i> and a negative form <i>(-vi)</i>.
 * <i>vi+</i> corresponds to matrix row/colum <i>2i</i> and <i>vi-</i>
 * corresponds to matrix row/colum <i>2i+1</i>. Each matrix entry stores a
 * constraint:
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
 * Octagon matrices are divided into <i>2x2</i> blocks. Block row/column
 * <i>i</i> contains the matrix rows/columns <i>2i</i> and <i>2i+1</i>.
 *
 * <p>
 * The same constraint can be represented by in two ways: <i>(+vj)-(+vi)≤c ⇔
 * (-vi)-(-vj)≤c ⇔ m(2i,2j)=c ⇔ m(2j+1,2i+1)=c</i>. The following ASCII art
 * shows matrix entries that effectively store the same constraints.
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
 * An octagon matrix is coherent iff matrix entries that effectively represent
 * the same constraint have the same values. This class ensures coherence by
 * storing only the block lower triangular matrix.
 *
 * <p>
 * Different octagons (matrices with different entries) may have the same
 * concretization. Closures can be used as a normal form for non-bottom
 * octagons.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class OctMatrix {

	public static final BiPredicate<OctValue, OctValue> sRelationEqual =
			(x, y) -> x.compareTo(y) == 0;
	public static final BiPredicate<OctValue, OctValue> sRelationLessThanOrEqual =
			(x, y) -> x.compareTo(y) <= 0;

	/**
	 * Empty octagon that stores constraints over the empty set of variables.
	 * Use {@link #NEW} and {@link #addVariables(int)} to create octagons of any
	 * size.
	 */
	public static final OctMatrix NEW = new OctMatrix(0);

	/**
	 * Used algorithm to compute the shortest path closure. All shortest path
	 * closure algorithms compute the same result, but may vary in terms of
	 * speed. The runtime of some algorithms depends on the content of the
	 * matrix.
	 */
	private static final Consumer<OctMatrix> sDefaultShortestPathClosure = OctMatrix::shortestPathClosurePrimitiveSparse;

	/**
	 * Size of this matrix (size = #rows = #columns). Size is always an even
	 * number.
	 *
	 * @see #variables()
	 */
	private final int mSize;

	/**
	 * Stores the entries (= elements) of this matrix.
	 * <p>
	 * Some entries are neglected because they are coherent to other entries
	 * (see documentation of this class). The stored entries and their indices
	 * are shown in the following ASCII art.
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
	 * The matrix is divided into 2x2 blocks. Every block that contains at least
	 * one element from the block lower triangular matrix is completely stored.
	 * Entries are stored row-wise from top to bottom, left to right.
	 *
	 * @see #indexOf(int, int)
	 */
	private final OctValue[] mEntries;

	/**
	 * Cached strong closure of this matrix. {@code null} if cache is empty.
	 * This cache has to be updated, if this matrix changes.
	 */
	private OctMatrix mStrongClosure;

	/**
	 * Cached tight closure of this matrix. {@code null} if cache is empty. This
	 * cache has to be updated, if this matrix changes.
	 */
	private OctMatrix mTightClosure;

	/**
	 * Creates a copy of this matrix. The copy can be used like a deep copy.
	 * Only the cached closures are shallow copies.
	 *
	 * @return Copy of this matrix
	 */
	public OctMatrix copy() {
		final OctMatrix copy = new OctMatrix(variables());
		System.arraycopy(mEntries, 0, copy.mEntries, 0, mEntries.length);
		copy.mStrongClosure = (mStrongClosure == this) ? copy : mStrongClosure;
		copy.mTightClosure = (mTightClosure == this) ? copy : mTightClosure;
		return copy;
	}

	/**
	 * Creates a new matrix by parsing a string representation of a matrix. The
	 * string representation must list the matrix entries row-wise, from top to
	 * bottom and left to right. The entries must be parsable by
	 * {@link OctValue#parse(String)} and be separated by any whitespace. Only
	 * entries of he block lower triangular matrix should be included. Line
	 * breaks for new rows of the matrix are not necessary.
	 * <p>
	 * Example string representation of a 4×4 matrix:
	 *
	 * <pre>
	 * 1 inf
	 * 3   4
	 * 5   6   7   8
	 * 9  10  11  12
	 * </pre>
	 *
	 * is the same as <code>1 inf 3 4 5 6 7 8 9 10 11 12</code>.
	 *
	 * @param m
	 *            String representation of the matrix to be created
	 * @return Parsed matrix
	 */
	public static OctMatrix parseBlockLowerTriangular(String m) {
		m = m.trim();
		final String[] entries = m.length() > 0 ? m.split("\\s+") : new String[0];
		final int matrixRows = (int) Math.sqrt(1.0 + 2 * entries.length) - 1;
		if (matrixRows % 2 != 0) {
			throw new IllegalArgumentException(
					"Number of entries does not match any 2x2 block lower triangular matrix.");
		}
		final OctMatrix oct = new OctMatrix(matrixRows / 2);
		for (int i = 0; i < entries.length; ++i) {
			oct.mEntries[i] = OctValue.parse(entries[i]);
		}
		return oct;
	}

	/**
	 * Creates a matrix of the given size, filled with random values. This
	 * methods uses {@link #random(int, double)} and sets the infinity
	 * probability to a random value.
	 *
	 * @param variables
	 *            Number of variables in the octagon
	 * @return Random matrix
	 */
	public static OctMatrix random(final int variables) {
		return random(variables, Math.random());
	}

	/**
	 * Creates a matrix of the given size, filled with random values. Matrix
	 * entries have the probability {@code infProbability} to be
	 * {@link OctValue#INFINITY}. Finite entries are random values from the
	 * interval [-10, 10).
	 *
	 * @param variables
	 *            Number of variables in the octagon
	 * @param infProbability
	 *            Probability that an entry will be infinity (0 = never, 1 =
	 *            always)
	 */
	public static OctMatrix random(final int variables, final double infProbability) {
		final OctMatrix m = new OctMatrix(variables);
		for (int row = 0; row < m.mSize; ++row) {
			final int maxCol = row | 1;
			for (int col = 0; col <= maxCol; ++col) {
				OctValue v;
				if (row == col) {
					v = OctValue.ZERO;
				} else if (Math.random() < infProbability) {
					v = OctValue.INFINITY;
				} else {
					v = new OctValue(ThreadLocalRandom.current().nextInt(-10, 10));
				}
				m.set(row, col, v);
			}
		}
		return m;
	}

	/**
	 * Creates a new matrix of the given size. Initially, the matrix entries are
	 * {@code null}.
	 *
	 * @param variables
	 *            Number of variables (= 2 * #rows = 2 * #columns) of the matrix
	 */
	public OctMatrix(final int variables) {
		mSize = variables * 2;
		mEntries = new OctValue[entriesInBlockLowerTriangular(variables)];
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
	public void fill(final OctValue fill) {
		for (int i = 0; i < mEntries.length; ++i) {
			mEntries[i] = fill;
		}
		mStrongClosure = mTightClosure = null;
	}

	/**
	 * Returns the number of rows (= number of columns) in this octagon matrix.
	 * Octagon matrices always have an even-numbered size, since every variable
	 * corresponds to two rows (and two columns) of the octagon matrix.
	 *
	 * @return size of this octagon matrix.
	 */
	public int getSize() {
		return mSize;
	}

	/**
	 * Returns the number of variables, stored by this octagon. Each variable
	 * corresponds to two rows and two columns of the octagon matrix.
	 *
	 * @return number of variables in this octagon
	 */
	public int variables() {
		return mSize / 2;
	}

	/**
	 * Reads an entry of this matrix. This method can also read entries from the
	 * block upper triangular matrix (which is not explicitly stored).
	 *
	 * @param row
	 *            Matrix row (zero-based)
	 * @param col
	 *            Matrix column (zero-based)
	 * @return Matrix entry in the given row and column
	 */
	public OctValue get(final int row, final int col) {
		return mEntries[indexOf(row, col)];
	}

	/**
	 * Writes an entry of this matrix. This method can also write entries of the
	 * block upper triangular matrix (which is not explicitly stored). Coherence
	 * is assured, which means that writing one entry also changes the coherent
	 * entry.
	 *
	 * @param row
	 *            Matrix row (zero-based)
	 * @param col
	 *            Matrix column (zero-based)
	 * @return Matrix entry in the given row and column
	 */
	public void set(final int row, final int col, final OctValue value) {
		assert value != null : "null is not a valid matrix entry.";
		mStrongClosure = mTightClosure = null;
		mEntries[indexOf(row, col)] = value;
	}

	/**
	 * Changes an entry of this matrix iff the new value is smaller than the old
	 * value. If the new value is not smaller than the old value, this matrix
	 * remains unchanged.
	 * <p>
	 * This method models the effect of {@code assume vCol - vRow <= newValue},
	 * where {@code vRow} and {@code vCol} are positive or negative forms of a
	 * program variable.
	 *
	 * @param row
	 *            Row of the matrix entry
	 * @param col
	 *            Column of the matrix entry
	 * @param newValue
	 *            New value of the matrix entry (must be smaller than the old
	 *            value to have an effect)
	 */
	public void setMin(final int row, final int col, final OctValue newValue) {
		assert newValue != null : "null is not a valid matrix entry.";
		final int index = indexOf(row, col);
		if (newValue.compareTo(mEntries[index]) < 0) {
			mEntries[index] = newValue;
			mStrongClosure = mTightClosure = null;
		}
	}

	/**
	 * Sets positive values on the main diagonal to zero. Negative values are
	 * kept, since they denote that this octagon is \bot. When encountering a
	 * negative value, this method exits early => positive values may remain on
	 * the diagonal.
	 *
	 * @return A value on the main diagonal was smaller than zero (=> negative
	 *         self loop => this=\bot)
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
			mEntries[idx] = OctValue.ZERO;
			// no need to reset cached closures
			// diagonal is always minimized on closure computation
			return false;
		}
		return sig < 0;
	}

	/**
	 * Computes the index of any matrix entry for the array {@link #mEntries}.
	 * Coherent matrix entries have the same index.
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
	 * Computes the index of an block lower triangular matrix entry for the
	 * array {@link #mEntries}. This method only works for entries of the block
	 * lower triangular matrix!
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
	 * Performs a binary element-wise (= point-wise) operation on matrices.
	 * {@code this} is the first operand and {@code other} is the second
	 * operand. Both operands remain unchanged.
	 *
	 * @param other
	 *            Second operand
	 * @param operator
	 *            Operation to be performed for each pair of entries
	 * @return Result of the operation
	 */
	public OctMatrix elementwiseOperation(final OctMatrix other,
			final BiFunction<OctValue, OctValue, OctValue> operator) {
		checkCompatibility(other);
		final OctMatrix result = new OctMatrix(variables());
		for (int i = 0; i < mEntries.length; ++i) {
			result.mEntries[i] = operator.apply(mEntries[i], other.mEntries[i]);
		}
		return result;
	}

	/**
	 * Checks a binary element-wise (= point-wise) relation on matrices.
	 * {@code this} is the left hand side and {@code other} is the right hand
	 * side of the relation. Both sides remain unchanged.
	 *
	 * @param other
	 *            Right hand side of the relation
	 * @param relation
	 *            Elementwise relation to be checked
	 * @return All pairs of corresponding entries were in the relation
	 */
	public boolean elementwiseRelation(final OctMatrix other, final BiPredicate<OctValue, OctValue> relation) {
		checkCompatibility(other);
		for (int i = 0; i < mEntries.length; ++i) {
			if (!relation.test(mEntries[i], other.mEntries[i])) {
				return false;
			}
		}
		return true;
	}

	public boolean elementwiseRelation(final OctMatrix other, final BiPredicate<OctValue, OctValue> relation,
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
	 * Checks whether a 2×2 block of this matrix is in an elementwise relation
	 * to another 2×2 block of (possibly another) matrix. Block row/column with
	 * index <i>i</i> contains the rows/columns <i>2i</i> and <i>2i+1</i>.
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
	 * @return All pairs of corresponding entries from the specified blocks were
	 *         in the relation
	 */
	public boolean blockwiseRelation(int bRow, int bCol, final OctMatrix other, int otherBRow, int otherBCol,
			final BiPredicate<OctValue, OctValue> relation) {
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
	 * Checks whether this and another matrix are compatible for a element-wise
	 * operation or relation. An exception is thrown for incompatible matrices.
	 * Matrixes are compatible if they have the same size.
	 *
	 * @param other
	 *            Other octagon
	 * @throws IllegalArgumentException
	 *             The matrices are incompatible
	 */
	private void checkCompatibility(final OctMatrix other) {
		if (other.mSize != mSize) {
			throw new IllegalArgumentException("Incompatible matrices");
		}
	}

	/**
	 * Computes the element-wise addition of this and another matrix.
	 *
	 * @param other
	 *            Other octagon
	 * @return Element-wise addition
	 */
	public OctMatrix add(final OctMatrix other) {
		return elementwiseOperation(other, OctValue::add);
	}

	/**
	 * Create a rearranged version of this matrix. Variables can be swapped,
	 * added, or removed.
	 *
	 * @param mapNewToOldVar
	 *            Array of length {@code n}, where {@code n} is the number of
	 *            variables inside the rearranged matrix. For variable {@code i}
	 *            of the rearranged matrix, {@code mapNewToOldVar[i]} is the
	 *            variable of the source (this) matrix or a negative number if
	 *            {@code i} is a fresh variable.
	 *
	 * @return Rearranged matrix.
	 *
	 * @see #copySelection(OctMatrix, Map)
	 */
	public OctMatrix rearrange(final int[] mapNewToOldVar) {
		final OctMatrix n = new OctMatrix(mapNewToOldVar.length);

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
		Arrays.fill(n.mEntries, freshSuffixStart, n.mEntries.length, OctValue.INFINITY);
		return n;
	}

	/**
	 * Computes the element-wise minimum of two matrices with the same size. The
	 * element-wise minimum is a meet operator for octagons (over-approximates
	 * the intersection of octagons).
	 *
	 * @param m
	 *            First matrix
	 * @param n
	 *            Second matrix
	 * @return Element-wise minimum
	 */
	public static OctMatrix min(final OctMatrix m, final OctMatrix n) {
		return m.elementwiseOperation(n, OctValue::min);
	}

	/**
	 * Computes the element-wise maximum of two matrices with the same size. The
	 * element-wise maximum is a join operator for octagons (over-approximates
	 * the union of octagons).
	 *
	 * @param m
	 *            First matrix
	 * @param n
	 *            Second matrix
	 * @return Element-wise minimum
	 */
	public static OctMatrix max(final OctMatrix m, final OctMatrix n) {
		OctMatrix result = m.elementwiseOperation(n, OctValue::max);
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
	 * Checks whether this and another matrix of the same size are equal, that
	 * is, if both have the same entries. Different octagon matrices may have
	 * the same concretization! Closures can be used as a normal form for
	 * non-bottom octagons.
	 *
	 * @param other
	 *            Other matrix
	 * @return The matrices are equal
	 */
	public boolean isEqualTo(final OctMatrix other) {
		if (this == other) {
			return true;
		}
		return elementwiseRelation(other, sRelationEqual);
	}

	/**
	 * Checks whether this and another octagon matrix of the same size are
	 * equal, considering that the order of variables was permuted in the other
	 * matrix.
	 * <p>
	 * The permutation must be known. If this octagon matrix uses the variable
	 * order <code>{v0, v1, v2}</code> and the other octagon matrix uses the
	 * variable order <code>{v1, v2, v0}</code>, then the permutation is
	 * <code>[2, 0, 1]</code>.
	 * <p>
	 * Different octagon matrices may have the same concretization! Closures can
	 * be used as a normal form for non-bottom octagons.
	 *
	 *
	 * @param permutation
	 *            Other matrix (possibly a permutation of this matrix)
	 * @param mapThisVarIndexToPermVarIndex
	 *            Map from variable indices (array index) of this octagon matrix
	 *            to the corresponding variable indices (array entries) of the
	 *            permuted octagon matrix. {@code null} for non-permuted
	 *            matrices.
	 * @return The matrices are equal
	 */
	public boolean isEqualTo(final OctMatrix permutation, final int[] mapThisVarIndexToPermVarIndex) {
		return elementwiseRelation(permutation, sRelationEqual, mapThisVarIndexToPermVarIndex);
	}

	/**
	 * Checks whether this octagon matrix is element-wise less or equal than
	 * another octagon matrix.
	 * <p>
	 * Note: <i>"not less-equal than"</i> does not necessarily mean <i>"greater
	 * than"</i>. OctMatrices are only partially ordered!
	 *
	 * @param other
	 *            Other octagon matrix
	 * @return This matrix is element-wise less than or equal to the other
	 *         matrix
	 */
	public boolean isLessEqualThan(final OctMatrix other) {
		return elementwiseRelation(other, sRelationLessThanOrEqual);
	}

	/**
	 * Returns the strong closure of this octagon matrix. The strong closure is
	 * only computed, if it is not already cached. The original cache is
	 * returned. Do not modify!
	 *
	 * @return Strong closure
	 */
	public OctMatrix cachedStrongClosure() {
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
	 * Computes the strong closure of this octagon matrix. The strong closure is
	 * a normal form for non-bottom octagon matrices over real-valued variables.
	 *
	 * @param shortestPathClosureAlgorithm
	 *            Algorithm to be used for the computation of the shortest path
	 *            closure
	 * @return Strong closure
	 */
	public OctMatrix strongClosure(final Consumer<OctMatrix> shortestPathClosureAlgorithm) {
		final OctMatrix strongClosure = copy();
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
	 * Returns the tight closure of this octagon matrix. The tight closure is
	 * only computed, if it is not already cached. The original cache is
	 * returned. Do not modify!
	 *
	 * @return Tight closure
	 */
	public OctMatrix cachedTightClosure() {
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
	 * Computes the tight closure of this octagon matrix. The tight closure is a
	 * normal form for non-bottom octagon matrices over integer variables.
	 *
	 * @param shortestPathClosureAlgorithm
	 *            Algorithm to be used for the computation of the shortest path
	 *            closure
	 * @return Tight closure
	 */
	public OctMatrix tightClosure(final Consumer<OctMatrix> shortestPathClosureAlgorithm) {
		final OctMatrix tightClosure;
		tightClosure = copy();
		if (!tightClosure.minimizeDiagonal()) { // this matrix is obviously
												// bottom
			shortestPathClosureAlgorithm.accept(tightClosure); // cached strong
																// closure is
																// not re-used
																// ...
			// ... because strong closure is unlikely to be in cache when tight
			// closure is needed
			tightClosure.tighteningInPlace();
		}
		tightClosure.mStrongClosure = mStrongClosure;
		tightClosure.mTightClosure = mTightClosure = tightClosure;
		return tightClosure;
	}

	/**
	 * Compute the shortest path closure in-place, using the naive
	 * Floyd-Warshall algorithm.
	 */
	protected void shortestPathClosureNaiv() {
		for (int k = 0; k < mSize; ++k) {
			for (int i = 0; i < mSize; ++i) {
				final OctValue ik = get(i, k);
				for (int j = 0; j < mSize; ++j) {
					final OctValue indirectRoute = ik.add(get(k, j));
					if (get(i, j).compareTo(indirectRoute) > 0) {
						set(i, j, indirectRoute);
					}
				}
			}
		}
	}

	/**
	 * Compute the shortest path closure in-place, using Singh's "Sparse
	 * Closure" algorithm
	 * (http://e-collection.library.ethz.ch/eserv/eth:8628/eth-8628-01.pdf).
	 * <p>
	 * This algorithm is based on Floyd-Warshall and runs on the full matrix.
	 * Finite matrix entries are indexed. Updates are computed using only the
	 * indexed entries.
	 */
	protected void shortestPathClosureFullSparse() {
		for (int k = 0; k < mSize; ++k) {
			final List<Integer> indexFiniteEntriesInColK = indexFiniteEntriesInColumn(k);
			final List<Integer> indexFiniteEntriesInRowK = indexFiniteEntriesInRow(k);
			for (final int i : indexFiniteEntriesInColK) {
				final OctValue ik = get(i, k);
				for (final int j : indexFiniteEntriesInRowK) {
					final OctValue kj = get(k, j);
					final OctValue indirectRoute = ik.add(kj);
					if (get(i, j).compareTo(indirectRoute) > 0) {
						set(i, j, indirectRoute);
					}
				}
			}
		}
	}

	/**
	 * Indexes the the finite entries in a matrix column.
	 *
	 * @param k
	 *            Column index
	 * @return Index of finite entries in column k (incoming edges of k)
	 */
	private List<Integer> indexFiniteEntriesInColumn(final int k) {
		final List<Integer> index = new ArrayList<>(mSize);
		for (int i = 0; i < mSize; ++i) {
			if (!get(i, k).isInfinity()) {
				index.add(i);
			}
		}
		return index;
	}

	/**
	 * Indexes the the finite entries in a matrix row.
	 *
	 * @param k
	 *            Row index
	 * @return Index of finite entries in row k (outgoing edges of k)
	 */
	private List<Integer> indexFiniteEntriesInRow(final int k) {
		final List<Integer> index = new ArrayList<>(mSize);
		for (int j = 0; j < mSize; ++j) {
			if (!get(k, j).isInfinity()) {
				index.add(j);
			}
		}
		return index;
	}

	/**
	 * Compute the shortest path closure in-place, using a sparse algorithm that
	 * iterates only the block lower triangular matrix.
	 * <p>
	 * This is a modification of {@link #shortestPathClosureFullSparse()}.
	 */
	protected void shortestPathClosureSparse() {
		List<Integer> indexFiniteEntriesInBlockCol = null;
		List<Integer> indexFiniteEntriesInBlockRow = null;
		for (int k = 0; k < mSize; ++k) {
			final int kk = k ^ 1;
			if (k < kk) { // k is even => entered new 2x2 block
				indexFiniteEntriesInBlockCol = indexFiniteEntriesInBlockColumn(k);
				indexFiniteEntriesInBlockRow = indexFiniteEntriesInBlockRow(k);
			}
			for (final int i : indexFiniteEntriesInBlockCol) {
				final OctValue ik = get(i, k);
				final OctValue ikk = get(i, kk);
				final int maxCol = i | 1;
				for (final int j : indexFiniteEntriesInBlockRow) {
					if (j > maxCol) {
						break;
					}
					final OctValue kj = get(k, j);
					final OctValue kkj = get(kk, j);
					final OctValue indirectRoute = OctValue.min(ik.add(kj), ikk.add(kkj));
					if (get(i, j).compareTo(indirectRoute) > 0) {
						set(i, j, indirectRoute);
					}
				}
			}
		}
	}

	/**
	 * Indexes the the finite entries in a matrix block column. The index
	 * contains only the row indices of finite entries in the block column k/2.
	 * The index can not be used to determine whether the finite entry is in
	 * column k or column k+1.
	 *
	 * @param k
	 *            First column index of the block column (always an even number)
	 * @return Index of finite entries in block column k/2 (incoming edges of k
	 *         and k+1)
	 */
	private List<Integer> indexFiniteEntriesInBlockColumn(final int k) {
		final List<Integer> index = new ArrayList<>(mSize);
		final int kk = k ^ 1;
		for (int i = 0; i < mSize; ++i) {
			if (!get(i, k).isInfinity() || !get(i, kk).isInfinity()) {
				index.add(i);
			}
		}
		return index;
	}

	/**
	 * Indexes the the finite entries in a matrix block row. The index contains
	 * only the column indices of finite entries in the block row k/2. The index
	 * can not be used to determine whether the finite entry is in row k or row
	 * k+1.
	 *
	 * @param k
	 *            First column index of the block row (always an even number)
	 * @return Index of finite entries in block row k/2 (outgoing edges of k and
	 *         k+1)
	 */
	private List<Integer> indexFiniteEntriesInBlockRow(final int k) {
		final List<Integer> index = new ArrayList<>(mSize);
		final int kk = k ^ 1;
		for (int j = 0; j < mSize; ++j) {
			if (!get(k, j).isInfinity() || !get(kk, j).isInfinity()) {
				index.add(j);
			}
		}
		return index;
	}

	/**
	 * Computes the shortest path closure in-place, as in
	 * {@link #shortestPathClosureSparse()}, while using only one primitive
	 * array instead of two java collections to represent the index.
	 */
	protected void shortestPathClosurePrimitiveSparse() {
		int[] rk = null; // indices of finite entries in rows k and k^1
		int[] ck = null; // indices of finite entries in columns k and k^1
		int indexLength = 0;
		for (int k = 0; k < mSize; ++k) {
			final int kk = k ^ 1;
			if (k < kk) { // k is even => entered new 2x2 block
				rk = new int[mSize];
				ck = new int[mSize];
				indexLength = primitiveIndexFiniteEntriesInBlockRowAndColumn(k, rk, ck);
			}
			for (int _i = 0; _i < indexLength; ++_i) {
				final int i = ck[_i];
				final OctValue ik = get(i, k);
				final OctValue ikk = get(i, kk);
				final int maxCol = i | 1;
				for (int _j = 0; _j < indexLength; ++_j) {
					final int j = rk[_j];
					if (j > maxCol) {
						break;
					}
					final OctValue kj = get(k, j);
					final OctValue kkj = get(kk, j);
					final OctValue indirectRoute = OctValue.min(ik.add(kj), ikk.add(kkj));
					if (get(i, j).compareTo(indirectRoute) > 0) {
						set(i, j, indirectRoute);
					}
				}
			}
		}
	}

	/**
	 * Indexes the the finite entries in block row k/2 and a block column k/2 at
	 * the same time. If the computed row index contains the value i, then there
	 * is a finite matrix entry at matrix index (i,k) or (i,k+1). If the
	 * computed column index contains the value i, then there is a finite matrix
	 * entry at matrix index (k,i), or (k+1,i).
	 * <p>
	 * The returned array has always the length {@link #getSize()}, but only the
	 * first n index entries are used. The length n of the index is the return
	 * value of this method. The row and column index always have the same
	 * length.
	 *
	 * @param k
	 *            First row/column index of the block row/column (always an even
	 *            number)
	 * @param rowIndex
	 *            Index of finite entries in block row k/2 (outgoing edges of k
	 *            and k+1). This index is not completely sorted! The values 2i
	 *            and 2i+1 are swapped.
	 * @param colIndex
	 *            Index of finite entries in block column k/2 (incoming edges of
	 *            k and k+1)
	 * @return Actual length of the row/column index
	 */
	private int primitiveIndexFiniteEntriesInBlockRowAndColumn(final int k, final int[] rowIndex,
			final int[] colIndex) {
		int indexLength = 0;
		final int kk = k ^ 1;
		for (int i = 0; i < mSize; ++i) {
			if (!get(i, k).isInfinity() || !get(i, kk).isInfinity()) {
				colIndex[indexLength] = i;
				rowIndex[indexLength] = i ^ 1;
				++indexLength;
			}
		}
		return indexLength;
	}

	/**
	 * Compute the shortest path closure in-place, using the closure algorithm
	 * of APRON (a library) as recalled by Singh
	 * (http://e-collection.library.ethz.ch/eserv/eth:8628/eth-8628-01.pdf).
	 * <p>
	 * This algorithm is based on Floyd-Warshall and iterates only the block
	 * lower triangular matrix.
	 */
	protected void shortestPathClosureApron() {
		for (int k = 0; k < mSize; ++k) {
			for (int i = 0; i < mSize; ++i) {
				final OctValue ik = get(i, k);
				final OctValue ikk = get(i, k ^ 1);
				final int maxCol = i | 1;
				for (int j = 0; j <= maxCol; ++j) {
					final OctValue kj = get(k, j);
					final OctValue kkj = get(k ^ 1, j);
					final OctValue indirectRoute = OctValue.min(ik.add(kj), ikk.add(kkj));
					if (get(i, j).compareTo(indirectRoute) > 0) {
						set(i, j, indirectRoute);
					}
				}
			}
		}
	}

	/**
	 * Computes the strong closure from this matrix in-place, as presented by
	 * Bagnara, Hill, and Zaffanella (https://arxiv.org/pdf/0705.4618v2).
	 * <p>
	 * This matrix has to be in shortest-path-closure form.
	 */
	private void strengtheningInPlace() {
		// blocks on the diagonal (upper, lower bounds) won't change by
		// strengthening
		// => iterate only 2x2 blocks that are _strictly_ below the main
		// diagonal
		for (int i = 2; i < mSize; ++i) {
			final OctValue ib = get(i, i ^ 1).half();
			final int maxCol = (i - 2) | 1;
			for (int j = 0; j <= maxCol; ++j) {
				final OctValue jb = get(j ^ 1, j).half();
				final OctValue b = ib.add(jb);
				if (get(i, j).compareTo(b) > 0) {
					set(i, j, b);
				}
			}
		}
	}

	/**
	 * Computes the tight closure of this matrix in-place, as presented by
	 * Bagnara, Hill, and Zaffanella (https://arxiv.org/pdf/0705.4618v2).
	 * <p>
	 * This matrix has to be in shortest-path-closure form.
	 */
	private void tighteningInPlace() {
		for (int i = 0; i < mSize; ++i) {
			final OctValue ib = get(i, i ^ 1).half().floor();
			final int maxCol = i | 1;
			for (int j = 0; j <= maxCol; ++j) {
				final OctValue jb = get(j ^ 1, j).half().floor();
				final OctValue b = ib.add(jb);
				if (get(i, j).compareTo(b) > 0) {
					set(i, j, b);
				}
			}
		}
	}

	/**
	 * Checks for negative self loops in the graph represented by this adjacency
	 * matrix. Self loops are represented by this matrix' diagonal entries.
	 * <p>
	 * <b>m</b> is strongly closed and has a negative self loop <=> <b>m</b> is
	 * empty in <b>R</b><br>
	 * <b>m</b> is tightly closed and has a negative self loop <=> <b>m</b> is
	 * empty in <b>Z</b>
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
	 * Widens this octagon by another one. Constraints that would be loosened by
	 * a normal join are immediately removed by this widening operator.
	 * <p>
	 * This widening operator was presented by Mine
	 * (http://www-apr.lip6.fr/~mine/publi/article-mine-ast01.pdf).
	 *
	 * @param n
	 *            Other octagon
	 * @return This octagon, widened with {@code n}
	 */
	public OctMatrix widenSimple(final OctMatrix n) {
		return elementwiseOperation(n, (mij, nij) -> mij.compareTo(nij) >= 0 ? mij : OctValue.INFINITY);
	}

	/**
	 * Widens this octagon by another one. Constraints that would be loosened by
	 * a normal join are loosened even more, using a binary exponential backoff.
	 * Constraints are removed, once the backoff reaches a given threshold. The
	 * threshold has to be finite to ensure stabilization of this widening
	 * operator.
	 *
	 * @param n
	 *            Other octagon
	 * @param threshold
	 *            Finite threshold (updated matrix entries > threshold will be
	 *            set to infinity)
	 * @return This octagon, widened with {@code n}
	 */
	public OctMatrix widenExponential(final OctMatrix n, final OctValue threshold) {
		final OctValue epsilon = new OctValue(1);
		final OctValue minusTwoEpsilon = epsilon.add(epsilon).negate();
		final OctValue oneHalfEpsilon = epsilon.half();
		return elementwiseOperation(n, (mij, nij) -> {
			if (mij.compareTo(nij) >= 0) {
				return mij;
			} else if (nij.compareTo(threshold) > 0) {
				return OctValue.INFINITY;
			}
			OctValue result;
			if (nij.compareTo(minusTwoEpsilon) <= 0) {
				result = nij.half(); // there is no -inf => will always converge
										// towards 0
			} else if (nij.signum() <= 0) {
				result = OctValue.ZERO;
			} else if (nij.compareTo(oneHalfEpsilon) <= 0) {
				result = epsilon;
			} else {
				result = nij.add(nij); // 2 * nij
			}
			return OctValue.min(result, threshold);
		});
	}

	/**
	 * Used for
	 * {@link OctMatrix#widenStepwise(OctMatrix, WideningStepSupplier)}.
	 *
	 * @author schaetzc@informatik.uni-freiburg.de
	 */
	public interface WideningStepSupplier {

		/**
		 * Returns a value used for widening. The widened value must be greater
		 * than or equal to the old value. The value infinity must be reached in
		 * an infinite number of steps for the widening operator to stabilize.
		 *
		 * @param val
		 *            Matrix entry which was increased by join and should be
		 *            widened.
		 * @return Value greater than or equal to {@code val}
		 */
		public OctValue nextWideningStep(final OctValue val);
	}

	/**
	 * Widens this octagon by another one. Constraints that would be loosened by
	 * a normal join are loosened even more, using a
	 * {@link WideningStepSupplier} to look up the next looser constraint.
	 * Usually, the widening steps are the literals from the analyzed program.
	 *
	 * @param n
	 *            Other octagon
	 * @param stepSupplier
	 *            Widening step supplier
	 * @return This octagon, widened with {@code n}
	 */
	public OctMatrix widenStepwise(final OctMatrix n, final WideningStepSupplier stepSupplier) {
		return elementwiseOperation(n, (mij, nij) -> {
			if (mij.compareTo(nij) >= 0) {
				return mij;
			}
			return stepSupplier.nextWideningStep(nij);
		});
	}

	/**
	 * Appends new block rows and block columns at the lower and right side of
	 * this matrix. New entries are initialized with {@link OctValue#INFINITY}.
	 * This matrix remains unchanged.
	 *
	 * <pre>
	 * # # . .     Result of this method
	 * # # . .
	 * . . . .     # entries of this matrix
	 * . . . .     . appended entries
	 * </pre>
	 *
	 * @param count
	 *            Number of block rows/columns to be appended
	 * @return New matrix with appended block rows and columns
	 */
	public OctMatrix addVariables(final int count) {
		if (count < 0) {
			throw new IllegalArgumentException("Cannot add " + count + " variables.");
		} else if (count == 0) {
			return this;
		}
		final OctMatrix n = new OctMatrix(variables() + count);
		System.arraycopy(mEntries, 0, n.mEntries, 0, mEntries.length);
		Arrays.fill(n.mEntries, mEntries.length, n.mEntries.length, OctValue.INFINITY);
		// cached closures are of different size and cannot be (directly) reused
		return n;
	}

	/**
	 * Removes a single block row and block column from this matrix. This matrix
	 * remains unchanged.
	 *
	 * @param varIndex
	 *            Index of the block row/column to be removed
	 * @return New matrix without the specified block row/column
	 *
	 * @see #removeVariables(Set)
	 */
	public OctMatrix removeVariable(final int varIndex) {
		return removeVariables(Collections.singleton(varIndex));
	}

	/**
	 * Removes multiple block rows and block columns. This matrix remains
	 * unchanged.
	 *
	 * @param varIndices
	 *            Indices of the block rows/columns to be removed
	 * @return New matrix without the specified block rows/columns
	 */
	public OctMatrix removeVariables(final Set<Integer> varIndices) {
		if (areVariablesLast(varIndices)) {
			return removeLastVariables(varIndices.size()); // note: sets cannot
															// contain
															// duplicates
		}
		return removeArbitraryVariables(varIndices);
	}

	/**
	 * Determines, whether a set of variables corresponds to the last block
	 * rows/columns in this matrix. A set of n variables is last, if the
	 * variables correspond to the n last block rows/columns.
	 *
	 * <pre>
	 *      # # . #                  # # # .
	 *      # # . #                  # # # .
	 *      . . . .                  # # # .
	 *      # # . #                  . . . .
	 * Selected variables       Selected variables
	 * (.) are NOT last         (.) are last
	 * </pre>
	 *
	 * @param varIndices
	 *            Block row/column indices
	 * @return The variables are last
	 */
	private boolean areVariablesLast(final Set<Integer> varIndices) {
		final List<Integer> varsDescending = new ArrayList<>(varIndices);
		Collections.sort(varsDescending);
		int vPrev = variables();
		for (final int v : varsDescending) {
			if (v < 0 || v >= variables()) {
				throw new IllegalArgumentException("Variable " + v + " does not exist.");
			} else if (v + 1 == vPrev) {
				vPrev = v;
			} else {
				return false;
			}
		}
		return true;
	}

	/**
	 * Removes multiple block rows and block columns from the end (bottom and
	 * right side) of this matrix. This matrix remains unchanged.
	 *
	 * @param varIndices
	 *            Number of block rows/columns to be removed
	 * @return New matrix without the specified block rows/columns
	 */
	private OctMatrix removeLastVariables(final int count) {
		if (count > variables()) {
			throw new IllegalArgumentException("Cannot remove more variables than exist.");
		}
		final OctMatrix n = new OctMatrix(variables() - count);
		System.arraycopy(mEntries, 0, n.mEntries, 0, n.mEntries.length);
		// cached closures are of different size and cannot be (directly) reused
		return n;
	}

	/**
	 * Removes multiple block rows and block columns from this matrix. This
	 * matrix remains unchanged.
	 * <p>
	 * This method is meant to cut out block rows/columns from the middle of a
	 * matrix. There are more efficient methods for special cases.
	 *
	 * @param varIndices
	 *            Indices of block rows/columns to be removed
	 * @return New matrix without the specified block rows/columns
	 */
	private OctMatrix removeArbitraryVariables(final Set<Integer> vars) {
		final OctMatrix n = new OctMatrix(variables() - vars.size()); // note:
																		// sets
																		// cannot
																		// contain
																		// duplicates
		int in = 0;
		for (int i = 0; i < mSize; ++i) {
			if (vars.contains(i / 2)) {
				// 2x2 block row shall be removed => continue in next 2x2 block
				// row
				++i;
				continue;
			}
			final int maxCol = i | 1;
			for (int j = 0; j <= maxCol; ++j) {
				if (vars.contains(j / 2)) {
					// 2x2 block column shall be removed => continue in next 2x2
					// block
					++j;
					continue;
				}
				n.mEntries[in++] = get(i, j);
			}
		}
		// cached closures are of different size and cannot be (directly) reused
		return n;
	}

	/**
	 * Copies selected block rows/columns of any matrix to this matrix. The
	 * matrices can be of different size. The source and target (this) matrix
	 * have to be different objects.
	 * <p>
	 * This method can also be used to permute the order of variables (that is,
	 * the order of block/rows columns). The following ASCII art shows what this
	 * method does. Each symbol from <code>· A B C D | -- ∞</code> depicts a 2x2
	 * block. The ∞-blocks are filled with {@link OctValue#INFINITY}.
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
	 *            Matrix to copy values from. Must be a different object than
	 *            this matrix.
	 * @param mapTargetToSourceVar
	 *            Indices of block rows/columns to be copied. The keys are
	 *            indices in the target (this) matrix. The values are indices in
	 *            the source (a different!) matrix. Values may be {@code null}
	 *            for new variables. Keys must not be {@code null}.
	 */
	protected void copySelection(final OctMatrix source, final Map<Integer, Integer> mapTargetToSourceVar,
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
					continue; // coherent block was already copied
				}
				final Integer sourceOther = mapTargetToSourceVar.get(targetOther);
				if (sourceOther == null || sourceVar == null) {
					setBlock(targetOther, targetVar, OctValue.INFINITY);
				} else {
					copyBlock(targetOther, targetVar, /* := */ source, sourceOther, sourceVar);
				}
			}
		}
	}

	private boolean containsTautology(final OctMatrix source, final Map<Integer, Integer> mapTargetToSourceVar,
			final int skipVarsLessThan, final int skipVarsBiggerEqualThan) {
		return source.mEntries == mEntries
				&& mapTargetToSourceVar.entrySet().stream().anyMatch(entry -> skipVarsLessThan <= entry.getKey()
						&& entry.getKey() < skipVarsBiggerEqualThan && entry.getKey().equals(entry.getValue()));
	}

	/** @see #copySelection(OctMatrix, Map, int) */
	protected void copySelection(final OctMatrix source, final Map<Integer, Integer> mapTargetToSourceVar) {
		copySelection(source, mapTargetToSourceVar, 0, Integer.MAX_VALUE);
	}

	// TODO document
	// - selectedSourceVars should not contain duplicates
	// - iteration order matters
	public OctMatrix appendSelection(final OctMatrix source, final Collection<Integer> selectedSourceVars) {
		final OctMatrix m = addVariables(selectedSourceVars.size());
		final Map<Integer, Integer> mapTargetVarToSourceVar = new HashMap<>();
		for (final Integer sourceVar : selectedSourceVars) {
			final int targetVar = mapTargetVarToSourceVar.size() + variables();
			final Integer prevValue = mapTargetVarToSourceVar.put(targetVar, sourceVar);
			assert prevValue == null : "Selection contained duplicate: " + sourceVar;
		}
		// TODO use skipVarsLessThan parameter
		m.copySelection(source, mapTargetVarToSourceVar);
		return m;
	}

	protected void copyBlock(int targetBRow, int targetBCol, final OctMatrix source, int sourceBRow, int sourceBCol) {
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

	protected void setBlock(int bRow, int bCol, final OctValue v) {
		bRow *= 2;
		bCol *= 2;
		for (int col = 0; col < 2; ++col) {
			for (int row = 0; row < 2; ++row) {
				set(bRow + row, bCol + col, v);
			}
		}
	}

	/**
	 * Assigns one variable to another variable in this matrix. {@code x := y;}
	 * <p>
	 * This method is exact. No precision is lost. Closure in advance is not
	 * necessary. Already closed matrices remain closed.
	 *
	 * @param targetVar
	 *            variable which will be changed
	 * @param sourceVar
	 *            variable which will be copied
	 */
	protected void assignVarCopy(final int targetVar, final int sourceVar) {
		if (targetVar == sourceVar) {
			return;
		}
		final boolean wasStronglyClosed = mStrongClosure == this;
		final boolean wasTightlyClosed = mTightClosure == this;

		final int t2 = targetVar * 2;
		final int s2 = sourceVar * 2;
		final int t21 = t2 + 1;
		final int s21 = s2 + 1;

		// "x == y" cannot be detected when imprecise "x + x <= 4" is copied
		minimizeDiagonalEntry(s2);
		minimizeDiagonalEntry(s2 + 1);

		// copy (block lower) block-row (including diagonal block)
		final int length = Math.min(s2, t2) + 2;
		System.arraycopy(mEntries, indexOfLower(s2, 0), mEntries, indexOfLower(t2, 0), length);
		System.arraycopy(mEntries, indexOfLower(s21, 0), mEntries, indexOfLower(t21, 0), length);

		// copy (block lower) block-column (without diagonal block)
		for (int row = length; row < mSize; ++row) {
			set(row, t2, get(row, s2));
			set(row, t21, get(row, s21));
		}

		copyBlock(targetVar, targetVar, this, sourceVar, sourceVar);

		// cached closures were reset by "set"
		if (wasStronglyClosed) {
			mStrongClosure = this;
		}
		if (wasTightlyClosed) {
			// tightly closed => all variables have integral values => copied
			// variable had integral value
			mTightClosure = this;
		}
	}

	/**
	 * Negates a variable. {@code x := -x;}
	 * <p>
	 * This method is exact. No precision is lost. Closure in advance is not
	 * necessary. Already closed matrices remain closed.
	 *
	 * @param targetVar
	 *            variable which will be negated
	 */
	protected void negateVar(final int targetVar) {
		final int t2 = targetVar * 2;
		final int t21 = t2 + 1;

		// swap (block lower) sub-rows of block-row (including diagonal block)
		final int t2RowStart = indexOf(t2, 0);
		final int t21RowStart = indexOf(t21, 0);
		final int length = t2 + 2;
		final OctValue[] tmpRow = new OctValue[length];
		System.arraycopy(mEntries, t2RowStart, tmpRow, 0, length); // tmp row :=
																	// upper row
		System.arraycopy(mEntries, t21RowStart, mEntries, t2RowStart, length); // upper
																				// row
																				// :=
																				// lower
																				// row
		System.arraycopy(tmpRow, 0, mEntries, t21RowStart, length); // lower row
																	// := tmp
																	// row

		// swap (block lower) sub-columns of block-column (including diagonal
		// block)
		for (int row = t2; row < mSize; ++row) {
			final int left = indexOfLower(row, t2);
			final int right = left + 1;
			final OctValue tmpVal = mEntries[left];
			mEntries[left] = mEntries[right];
			mEntries[right] = tmpVal;
		}

		if (mStrongClosure != this) {
			mStrongClosure = null;
		}
		if (mTightClosure != this) {
			mTightClosure = null;
		}
	}

	/**
	 * Adds a constant to a variable. {@code v := v + c;} The constant may also
	 * be negative.
	 * <p>
	 * This method is exact. No precision is lost. Closure in advance is not
	 * necessary. Already closed matrices remain closed.
	 *
	 * @param targetVar
	 *            variable to be incremented
	 * @param constant
	 *            summand
	 */
	protected void incrementVar(final int targetVar, final OctValue constant) {
		final int t2 = targetVar * 2;
		final int t21 = t2 + 1;

		// increment block-column, block-row is incremented by coherence
		for (int row = 0; row < mSize; ++row) {
			if (row / 2 == targetVar) {
				continue; // block (v, v) is processed after this loop
			}
			final int iT2 = indexOf(row, t2); // left sub-column of block-column
			final int iT21 = indexOf(row, t21); // right ...
			mEntries[iT2] = mEntries[iT2].add(constant); // (v + c) − ? ≤ ? <=>
															// v − ? ≤ ?
			mEntries[iT21] = mEntries[iT21].subtract(constant); // −(v + c) − ?
																// ≤ ? <=> −v −
																// ? ≤ ? − c
		}

		final OctValue doubleConstant = constant.add(constant);
		final int iUpperBound2 = indexOf(t21, t2);
		final int iLowerBound2 = indexOf(t2, t21);
		mEntries[iUpperBound2] = mEntries[iUpperBound2].add(doubleConstant);
		mEntries[iLowerBound2] = mEntries[iLowerBound2].subtract(doubleConstant);

		if (mStrongClosure != this) {
			mStrongClosure = null;
		}
		if (mTightClosure != this) {
			assert constant.isInfinity() || AbsIntUtil.isIntegral(constant.getValue()) : "int incremented by real";
			mTightClosure = null;
		}
	}

	protected void assignVarConstant(final int targetVar, final OctValue constant) {
		havocVar(targetVar);
		final int t2 = targetVar * 2;
		final int t21 = t2 + 1;
		final OctValue doubleConstant = constant.add(constant);
		set(t2, t21, doubleConstant.negate());
		set(t21, t2, doubleConstant);
		// cached closures were already reset by "set"
	}

	protected void assumeVarConstant(final int targetVar, final OctValue constant) {
		final int t2 = targetVar * 2;
		final int t21 = t2 + 1;
		final OctValue doubleConstant = constant.add(constant);
		setMin(t2, t21, doubleConstant.negate());
		setMin(t21, t2, doubleConstant);
		// cached closures were already reset by "set"
	}

	protected void assignVarInterval(final int targetVar, final OctValue min, final OctValue max) {
		havocVar(targetVar);
		final int t2 = targetVar * 2;
		final int t21 = t2 + 1;
		set(t2, t21, min.add(min).negateIfNotInfinity());
		set(t21, t2, max.add(max));
		// cached closures were already reset by "set"
	}

	protected void assumeVarInterval(final int targetVar, final OctValue min, final OctValue max) {
		final int t2 = targetVar * 2;
		final int t21 = t2 + 1;
		setMin(t2, t21, min.add(min).negateIfNotInfinity());
		setMin(t21, t2, max.add(max));
		// cached closures were already reset by "set"
	}

	// var1 + var2 <= constant
	protected void assumeVarRelationLeConstant(int var1, final boolean var1Negate, int var2, final boolean var2Negate,
			final OctValue constant) {
		var1 *= 2;
		var2 *= 2;
		if (!var1Negate) {
			var1 = var1 | 0b1; // negative form of var1
		}
		if (var2Negate) {
			var2 = var2 | 0b1; // negative form of var2
		}
		setMin(var1, var2, constant);
	}

	protected void havocVar(final int targetVar) {
		final int t2 = targetVar * 2;
		final int t21 = t2 + 1;

		// Set block-column. Block-row is set by coherence.
		for (int row = 0; row < mSize; ++row) {
			mEntries[indexOf(row, t2)] = mEntries[indexOf(row, t21)] = OctValue.INFINITY;
		}
		set(t2, t2, OctValue.ZERO);
		set(t21, t21, OctValue.ZERO);

		// cached closures were already reset by "set"
	}

	/**
	 * Computes the percentage of infinity-entries in the block lower half of
	 * this matrix. Empty matrices have a infinity percentage of
	 * {@link Double#NaN}.
	 *
	 * @return Percentage of infinity-entries in the block lower half of this
	 *         matrix.
	 */
	public double infinityPercentageInBlockLowerHalf() {
		if (mEntries.length == 0) {
			return Double.NaN;
		}
		int infCounter = 0;
		for (final OctValue v : mEntries) {
			if (v.isInfinity()) {
				++infCounter;
			}
		}
		return infCounter / (double) mEntries.length;
	}

	public List<Term> getTerm(final Script script, final Term[] vars) {
		final List<Term> rtr = new ArrayList<>(variables() * variables());
		for (int row = 0; row < 2 * variables(); ++row) {
			final Term rowVar = selectVar(script, row, vars);
			// iterate only block lower triangular matrix (skip coherent upper
			// part)
			for (int col = 0; col < (row / 2 + 1) * 2; ++col) {
				final OctValue entry = get(row, col);
				if (col == row) {
					if (entry.signum() < 0) {
						return Collections.singletonList(script.term("false")); // constraint
																				// of
																				// the
																				// form
																				// (0
																				// <=
																				// -1)
					}
					continue; // constraint of the form (0 <= 1)
				}
				final Term colVar = selectVar(script, col, vars);
				rtr.add(createBoundedDiffTerm(script, colVar, rowVar, entry));
			}
		}
		return rtr;
	}

	// returns variable in positive or negative form, depending on row or column
	private static Term selectVar(final Script script, final int rowCol, final Term[] vars) {
		final Term posNegVar = vars[rowCol / 2];
		if (rowCol % 2 == 1) {
			return script.term("-", posNegVar);
		}
		return posNegVar;
	}

	// returns minuend - subtrahend <= bound
	private static Term createBoundedDiffTerm(final Script script, Term minuend, Term subtrahend,
			final OctValue bound) {
		if (bound.isInfinity()) {
			return script.term("true");
		}
		final Term tBound;
		final Term t = minuend;
		final boolean minuendIsInt = SmtSortUtils.isIntSort(t.getSort());
		final Term t1 = subtrahend;
		final boolean subtrahendIsInt = SmtSortUtils.isIntSort(t1.getSort());
		if (minuendIsInt && subtrahendIsInt) {
			tBound = SmtUtils.constructIntValue(script, bound.getValue().round(new MathContext(0, RoundingMode.FLOOR)).toBigIntegerExact());
		} else {
			tBound = script.decimal(bound.getValue());
			if (minuendIsInt) {
				minuend = script.term("to_real", minuend);
			} else if (subtrahendIsInt) {
				subtrahend = script.term("to_real", subtrahend);
			}
		}
		return script.term("<=", script.term("-", minuend, subtrahend), tBound);
	}

	@Override
	public String toString() {
		return toStringHalf();
	}

	/**
	 * @return Multi-line string representation of this matrix (including the
	 *         coherent, block upper triangular part)
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
	 * @return Multi-line string representation of this block lower triangular
	 *         matrix
	 */
	public String toStringHalf() {
		final StringBuilder sb = new StringBuilder();
		int n = 2; // input of integer sequence floor(n^2 / 2 -1)
		int rowEnd = 1; // index of last entry in current row (= output of
						// integer sequence)
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

	/**
	 * @return Indices of variables which have constraints (that is, at least on
	 *         entry < infinity).
	 */
	public Set<Integer> variablesWithConstraints() {
		final Set<Integer> varsWithConstraints = new HashSet<>();
		for (int row = 0; row < mSize; ++row) {
			final int maxCol = row | 1;
			for (int col = 0; col <= maxCol; ++col) {
				final OctValue entry = get(row, col);
				final boolean hasConstraint = !entry.isInfinity() || (row == col && entry.signum() < 0);
				if (hasConstraint) {
					varsWithConstraints.add(row / 2);
					varsWithConstraints.add(col / 2);
				}
			}
		}
		return varsWithConstraints;
	}
}
