/*
 * Copyright (C) 2015-2016 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
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
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Consumer;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.NumUtil;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.TypeUtil;
import de.uni_freiburg.informatik.ultimate.util.BidirectionalMap;

/**
 * Matrix representation of octagons,
 * based on A. Miné's "The octagon abstract domain" (https://www-apr.lip6.fr/~mine/publi/article-mine-ast01.pdf).
 * 
 * <p>
 * Octagons store constraints of the form <i>±vi ± vj ≤ c</i> over numerical variables
 * <i>{v0, v1, ..., v(n-1)}</i>. An octagon over <i>n</i> variables is a <i>2n×2n</i> matrix.
 * Matrix indices are zero-based. Names and types of the variables are not stored by the octagon.
 * Each variable <i>vi</i> has two forms, a positive form <i>(+vi)</i> and a negative form <i>(-vi)</i>.
 * <i>vi+</i> corresponds to matrix row/colum <i>2i</i> and <i>vi-</i> corresponds to matrix row/colum <i>2i+1</i>.
 * Each matrix entry stores a constraint:
 * <table>
 * <thead>
 *   <tr><th>Constraint</th><th>Corresponding matrix entry</th></tr>
 * <thead>
 * <tbody>
 *   <tr><td><i>(+vj) - (+vi) ≤ c</i></td> <td><i>m(2i,   2j) = c<i></td></tr>
 *   <tr><td><i>(+vj) - (-vi) ≤ c</i></td> <td><i>m(2i+1, 2j) = c<i></td></tr>
 *   <tr><td><i>(-vj) - (+vi) ≤ c</i></td> <td><i>m(2i,   2j+1) = c<i></td></tr>
 *   <tr><td><i>(-vj) - (-vi) ≤ c</i></td> <td><i>m(2i+1, 2j+1) = c<i></td></tr>
 * </tbody>
 * </table>
 * Octagon matrices are divided into <i>2x2</i> blocks.
 * Block row/column <i>i</i> contains the matrix rows/columns <i>2i</i> and <i>2i+1</i>.
 * 
 * <p>
 * The same constraint can be represented by in two ways:
 * <i>(+vj)-(+vi)≤c ⇔ (-vi)-(-vj)≤c ⇔ m(2i,2j)=c ⇔ m(2j+1,2i+1)=c</i>.
 * The following ASCII art shows matrix entries that effectively store the same constraints.
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
 * An octagon matrix is coherent iff matrix entries that effectively represent the same constraint have the same values.
 * This class ensures coherence by storing only the block lower triangular matrix.
 * 
 * <p>
 * Different octagons (matrices with different entries) may have the same concretization.
 * Closures can be used as a normal form for non-bottom octagons.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class OctMatrix {

	/**
	 * Empty octagon that stores constraints over the empty set of variables.
	 * Use {@link #NEW} and {@link #addVariables(int)} to create octagons of any size.
	 */
	public final static OctMatrix NEW = new OctMatrix(0);

	/**
	 * Used algorithm to compute the shortest path closure.
	 * All shortest path closure algorithms compute the same result, but may vary in terms of speed.
	 * The runtime of some algorithms depends on the content of the matrix.
	 */
	private final static Consumer<OctMatrix> sDefaultShortestPathClosure = OctMatrix::shortestPathClosurePrimitiveSparse;

//	// Code to generate closure benchmark.
//	// Writes a string representation of this matrix to a file, each time a closure is computed.
//	private final static Consumer<OctMatrix> sDefaultShortestPathClosure = m -> {
//		if (m.mSize <= 0) {
//			return;
//		}
//		String s = m.toStringLower();
//		BufferedWriter bw;
//		try {
//			bw = new BufferedWriter(new FileWriter(makeFilename()), s.length() * 2);
//			try {
//				bw.write(s);
//			} finally {
//				bw.close();
//			}
//		} catch (IOException e) {
//			throw new AssertionError("Could not write benchmark file.", e);
//		}
//		m.shortestPathClosurePrimitiveSparse();
//	};
//
//	private static String makeFilename() {
//		int i;
//		synchronized (OctMatrix.class) {
//			i = ++sFileNameCounter;
//		}
//		return "/tmp/closureBenchmark/" + String.format("%08d", i);
//	}
//
//	private static volatile int sFileNameCounter = 0;

	/**
	 * Size of this matrix (size = #rows = #columns). Size is always an even number.
	 * 
	 * @see #variables()
	 */
	private final int mSize;

	/**
	 * Stores the elements of this matrix.
	 * <p>
	 * Some elements are neglected because they are coherent to other elements (see documentation of this class). The
	 * stored elements and their indices are shown in the following ASCII art.
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
	 * triangular matrix is completely stored. Elements are stored row-wise from top to bottom, left to right.
	 * 
	 * @see #indexOf(int, int)
	 */
	private final OctValue[] mElements;

	/**
	 * Cached strong closure of this matrix.
	 * {@code null} if cache is empty. This cache has to be updated, if this matrix changes.
	 */
	private OctMatrix mStrongClosure;

	/**
	 * Cached tight closure of this matrix.
	 * {@code null} if cache is empty. This cache has to be updated, if this matrix changes.
	 */
	private OctMatrix mTightClosure;

	/**
	 * Creates a copy of this matrix.
	 * The copy can be used like a deep copy. Only the cached closures are shallow copies.
	 * 
	 * @return Copy of this matrix
	 */
	public OctMatrix copy() {
		final OctMatrix copy = new OctMatrix(mSize);
		System.arraycopy(this.mElements, 0, copy.mElements, 0, mElements.length);
		copy.mStrongClosure = (mStrongClosure == this) ? copy : mStrongClosure;
		copy.mTightClosure = (mTightClosure == this) ? copy : mTightClosure;
		return copy;
	}

	/**
	 * Creates a new matrix by parsing a string representation of a matrix.
	 * The string representation must list the matrix entries row-wise, from top to bottom and left to right.
	 * The entries must be parsable by {@link OctValue#parse(String)} and be separated by any whitespace.
	 * Only entries of he block lower triangular matrix should be included.
	 * Line breaks for new rows of the matrix are not necessary.
	 * <p>
	 * Example string representation of a 4×4 matrix:
	 * <pre>
	 * 1 inf
	 * 3   4
	 * 5   6   7   8
	 * 9  10  11  12
	 * </pre>
	 * is the same as <code>1 inf 3 4 5 6 7 8 9 10 11 12</code>.
	 * 
	 * @param m String representation of the matrix to be created
	 * @return Parsed matrix
	 */
	public static OctMatrix parseBlockLowerTriangular(String m) {
		m = m.trim();
		final String[] elements = m.length() > 0 ? m.split("\\s+") : new String[0];
		int size = (int) (Math.sqrt(2 * elements.length + 1) - 1);
		if (size % 2 != 0) {
			throw new IllegalArgumentException(
					"Number of elements does not match any 2x2 block lower triangular matrix.");
		}
		final OctMatrix oct = new OctMatrix(size);
		for (int i = 0; i < elements.length; ++i) {
			oct.mElements[i] = OctValue.parse(elements[i]);
		}
		return oct;
	}

	/**
	 * Creates a matrix of the given size, filled with random values.
	 * This methods uses {@link #random(int, double)} and sets the infinity probability to a random value.
	 * 
	 * @param variables Number of variables in the octagon
	 * @return Random matrix
	 */
	public static OctMatrix random(final int variables) {
		return random(variables, Math.random());
	}

	/**
	 * Creates a matrix of the given size, filled with random values.
	 * Matrix entries have the probability {@code infProbability} to be {@link OctValue#INFINITY}.
	 * Finite entries are random values from the interval [-10, 10).
	 * 
	 * @param variables Number of variables in the octagon
	 * @param infProbability Probability that an element will be infinity (0 = never, 1 = always)
	 */
	public static OctMatrix random(final int variables, final double infProbability) {
		final OctMatrix m = new OctMatrix(variables * 2);
		for (int i = 0; i < m.mSize; ++i) {
			int maxCol = i | 1;
			for (int j = 0; j <= maxCol; ++j) {
				OctValue v;
				if (i == j) {
					v = OctValue.ZERO;
				} else if (Math.random() < infProbability) {
					v = OctValue.INFINITY;
				} else {
					v = new OctValue((int) (Math.random() * 20 - 10));
				}
				m.set(i, j, v);
			}
		}
		return m;
	}

	/**
	 * Creates a new matrix of the given size.
	 * Initially, the matrix entries are {@code null}.
	 * 
	 * @param size Size (= #rows = #columns) of the matrix
	 */
	protected OctMatrix(final int size) {
		mSize = size;
		mElements = new OctValue[size * size / 2 + size];
	}

	/**
	 * Fill this matrix with a given value.
	 * 
	 * @param fill Value to be used for all entries
	 */
	protected void fill(final OctValue fill) {
		for (int i = 0; i < mElements.length; ++i) {
			mElements[i] = fill;
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
	 * Returns the number of variables, stored by this octagon.
	 * Each variable corresponds to two rows and two columns of the octagon matrix.
	 * 
	 * @return number of variables in this octagon
	 */
	public int variables() {
		return mSize / 2;
	}

	/**
	 * Reads an entry of this matrix.
	 * This method can also read entries from the block upper triangular matrix (which is not explicitly stored).
	 * 
	 * @param row Matrix row (zero-based)
	 * @param col Matrix column (zero-based)
	 * @return Matrix entry in the given row and column
	 */
	public OctValue get(final int row, final int col) {
		return mElements[indexOf(row, col)];
	}

	/**
	 * Writes an entry of this matrix.
	 * This method can also write entries of the block upper triangular matrix (which is not explicitly stored).
	 * Coherence is assured, which means that writing one entry also changes the coherent entry.
	 * 
	 * @param row Matrix row (zero-based)
	 * @param col Matrix column (zero-based)
	 * @return Matrix entry in the given row and column
	 */
	protected void set(final int row, final int col, final OctValue value) {
		assert value != null : "null is not a valid matrix element.";
		mStrongClosure = mTightClosure = null;
		mElements[indexOf(row, col)] = value;
	}

	/**
	 * Changes an entry of this matrix iff the new value is smaller than the old value. If the new value is not smaller
	 * than the old value, this matrix remains unchanged.
	 * <p>
	 * This method models the effect of {@code assume vCol - vRow <= newValue}, where {@code vRow} and {@code vCol} are
	 * positive or negative forms of a program variable.
	 * 
	 * @param row Row of the matrix entry
	 * @param col Column of the matrix entry
	 * @param newValue New value of the matrix entry (must be smaller than the old value to have an effect)
	 */
	protected void setMin(final int row, final int col, final OctValue newValue) {
		assert newValue != null : "null is not a valid matrix element.";
		mStrongClosure = mTightClosure = null;
		final int index = indexOf(row, col);
		if (newValue.compareTo(mElements[index]) < 0) {
			mElements[index] = newValue;
			mStrongClosure = mTightClosure = null;
		}
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
			minimizeDiagonalElement(i);
		}
		return false;
	}

	/**
	 * Updates a diagonal entry {@code x} with {@code min(x,0)}.
	 * @param rowCol Row (= column) of the diagonal entry
	 */
	private void minimizeDiagonalElement(final int rowCol) {
		final int idx = indexOfLower(rowCol, rowCol);
		final int sig = mElements[idx].signum();
		if (sig > 0) {
			mElements[idx] = OctValue.ZERO;
			// no need to reset cached closures -- diagonal is always minimized on closure computation
		}
	}

	/**
	 * Computes the index of any matrix entry for the array {@link #mElements}.
	 * Coherent matrix entries have the same index.
	 * 
	 * @param row Matrix row
	 * @param col Matrix column
	 * @return Index (for {@link #mElements}) of the given matrix entry
	 */
	private int indexOf(final int row, final int col) {
		assert row < mSize && col < mSize : row + "," + col + " is not an index for matrix of size " + mSize + ".";
		if (row < col) {
			return indexOfLower(col ^ 1, row ^ 1);
		}
		return indexOfLower(row, col);
	}

	/**
	 * Computes the index of an block lower triangular matrix entry for the array {@link #mElements}.
	 * This method only works for entries of the block lower triangular matrix!
	 * 
	 * @param row Matrix row
	 * @param col Matrix column
	 * @return Index (for {@link #mElements}) of the given matrix entry
	 * 
	 * @see #indexOf(int, int)
	 */
	private int indexOfLower(final int row, final int col) {
		return col + (row + 1) * (row + 1) / 2;
	}

	/**
	 * Performs a binary element-wise operation on matrices.
	 * {@code this} is the first operand and {@code other} is the second operand.
	 * Both operands remain unchanged.
	 * 
	 * @param other Second operand
	 * @param operator Operation to be performed for each pair of entries
	 * @return Result of the operation
	 */
	public OctMatrix elementwiseOperation(
			final OctMatrix other, final BiFunction<OctValue, OctValue, OctValue> operator) {
		checkCompatibility(other);
		final OctMatrix result = new OctMatrix(mSize);
		for (int i = 0; i < mElements.length; ++i) {
			result.mElements[i] = operator.apply(mElements[i], other.mElements[i]);
		}
		return result;
	}

	/**
	 * Checks a binary element-wise relation on matrices.
	 * {@code this} is the left hand side and {@code other} is the right hand side of the relation.
	 * Both sides remain unchanged.
	 * 
	 * @param other Right hand side of the relation
	 * @param relation Relation to be checked for each pair of entries
	 * @return All pairs of entries were in the relation 
	 */
	public boolean elementwiseRelation(final OctMatrix other, final BiFunction<OctValue, OctValue, Boolean> relation) {
		checkCompatibility(other);
		for (int i = 0; i < mElements.length; ++i) {
			if (!relation.apply(mElements[i], other.mElements[i])) {
				return false;
			}
		}
		return true;
	}

	
	/**
	 * Checks whether this and another matrix are compatible for a element-wise operation or relation.
	 * An exception is thrown for incompatible matrices.
	 * 
	 * @param other Other octagon
	 * @throws IllegalArgumentException The matrices are incompatible
	 */
	private void checkCompatibility(final OctMatrix other) {
		if (other.mSize != mSize) {
			throw new IllegalArgumentException("Incompatible matrices");
		}
	}

	/**
	 * Computes the element-wise addition of this and another matrix.
	 * 
	 * @param other Other octagon
	 * @return Element-wise addition
	 */
	public OctMatrix add(final OctMatrix other) {
		return elementwiseOperation(other, OctValue::add);
	}

	/**
	 * Computes the element-wise minimum of two matrices with the same size.
	 * The element-wise minimum is a meet operator for octagons (over-approximates the intersection of octagons).
	 * 
	 * @param m First matrix
	 * @param n Second matrix
	 * @return Element-wise minimum
	 */
	public static OctMatrix min(final OctMatrix m, final OctMatrix n) {
		return m.elementwiseOperation(n, OctValue::min);
	}

	/**
	 * Computes the element-wise maximum of two matrices with the same size.
	 * The element-wise maximum is a join operator for octagons (over-approximates the union of octagons).
	 * 
	 * @param m First matrix
	 * @param n Second matrix
	 * @return Element-wise minimum
	 */
	public static OctMatrix max(final OctMatrix m, final OctMatrix n) {
		return m.elementwiseOperation(n, OctValue::max);
		// TODO set cached closure of result: a and b are closed ==> max(a,b) are closed
	}

	/**
	 * Checks whether this and another matrix of the same size are equal, that is, if both have the same entries.
	 * Different octagon matrices may have the same concretization!
	 * Closures can be used as a normal form for non-bottom octagons.
	 * 
	 * @param other Other matrix
	 * @return The matrices are equal
	 */
	public boolean isEqualTo(final OctMatrix other) {
		if (this == other) {
			return true;
		}
		return elementwiseRelation(other, (x, y) -> x.compareTo(y) == 0);
	}

	/**
	 * Checks whether this and another octagon matrix of the same size are
	 * equal, considering that the order of variables was permutated in the
	 * other matrix.
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
	 * @param permutation Other matrix (possibly a permutation of this matrix)
	 * @param mapThisVarIndexToPermVarIndex
	 *            Map from variable indices (array index) of this octagon matrix
	 *            to the corresponding variable indices (array entries) of the permuted octagon matrix
	 * @return The matrices are equal
	 */
	public boolean isEqualToPermutation(final OctMatrix permutation, final int[] mapThisVarIndexToPermVarIndex) {
		for (int bRow = 0; bRow < variables(); ++bRow) {
			// compare only block lower triangular part (upper part is coherent)
			for (int bCol = 0; bCol <= bRow; ++bCol) {
				final int permBRow = mapThisVarIndexToPermVarIndex[bRow];
				final int permBCol = mapThisVarIndexToPermVarIndex[bCol];
				if (!isBlockEqualTo(bRow, bCol, permutation, permBRow, permBCol)) {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * Checks whether a 2×2 block of this matrix equals another 2×2 block of another matrix.
	 * Block row/column with index <i>i</i> contains the rows/columns <i>2i</i> and <i>2i+1</i>.
	 * 
	 * @param bRow Block row index in this matrix
	 * @param bCol Block column index in this matrix
	 * @param other Other matrix
	 * @param otherBRow Block row index in other matrix
	 * @param otherBCol Block column index in the other matrix
	 * @return The blocks are equal
	 */
	public boolean isBlockEqualTo(int bRow, int bCol, final OctMatrix other, int otherBRow, int otherBCol) {
		bRow *= 2;
		bCol *= 2;
		otherBRow *= 2;
		otherBCol *= 2;
		for (int j = 0; j < 2; ++j) {
			for (int i = 0; i < 2; ++i) {
				if (get(bRow + i, bCol + j).compareTo((other.get(otherBRow + i, otherBCol + j))) != 0) {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * Checks whether this octagon matrix is element-wise less or equal than another octagon matrix.
	 * <p>
	 * Note: <i>"not less-equal than"</i> does not necessarily mean <i>"greater than"</i>.
	 * OctMatrices are only partially ordered!
	 * 
	 * @param other Other octagon matrix
	 * @return This matrix is element-wise less than or equal to the other matrix
	 */
	public boolean isLessEqualThan(final OctMatrix other) {
		return elementwiseRelation(other, (x, y) -> x.compareTo(y) <= 0);
	}

	/**
	 * Returns the strong closure of this octagon matrix.
	 * The strong closure is only computed, if it is not already cached.
	 * The original cache is returned. Do not modify!
	 * 
	 * @return Strong closure
	 */
	public OctMatrix cachedStrongClosure() {
		if (mStrongClosure != null) {
			return mStrongClosure;
		}
		return strongClosure(sDefaultShortestPathClosure);
	}

	/** @return The strong closure of this matrix was already computed and cached */
	public boolean hasCachedStrongClosure() {
		return mStrongClosure != null;
	}

	/**
	 * Computes the strong closure of this octagon matrix.
	 * The strong closure is a normal form for non-bottom octagon matrices over real-valued variables.
	 * 
	 * @param shortestPathClosureAlgorithm
	 *            Algorithm to be used for the computation of the shortest path closure
	 * @return Strong closure
	 */
	public OctMatrix strongClosure(final Consumer<OctMatrix> shortestPathClosureAlgorithm) {
		final OctMatrix sc = copy();
		final boolean obviouslyBottom = sc.minimizeDiagonal();
		if (!obviouslyBottom) {
			shortestPathClosureAlgorithm.accept(sc);
			sc.strengtheningInPlace();
		}
		sc.mStrongClosure = mStrongClosure = sc;
		sc.mTightClosure = mTightClosure;
		return sc;
	}

	/**
	 * Returns the tight closure of this octagon matrix.
	 * The tight closure is only computed, if it is not already cached.
	 * The original cache is returned. Do not modify!
	 * 
	 * @return Tight closure
	 */
	public OctMatrix cachedTightClosure() {
		if (mTightClosure != null) {
			return mTightClosure;
		}
		return tightClosure(sDefaultShortestPathClosure);
	}

	/** @return The tight closure of this matrix was already computed and cached */
	public boolean hasCachedTightClosure() {
		return mTightClosure != null;
	}
	
	/**
	 * Computes the tight closure of this octagon matrix.
	 * The tight closure is a normal form for non-bottom octagon matrices over integer variables.
	 * 
	 * @param shortestPathClosureAlgorithm
	 *            Algorithm to be used for the computation of the shortest path closure
	 * @return Tight closure
	 */
	public OctMatrix tightClosure(final Consumer<OctMatrix> shortestPathClosureAlgorithm) {
		OctMatrix tc;
		tc = copy();
		boolean isObviouslyBottom = tc.minimizeDiagonal();
		if (!isObviouslyBottom) {
			shortestPathClosureAlgorithm.accept(tc); // cached strong closure is not re-used ...
			// ... because strong closure is unlikely to be in cache when tight closure is needed
			tc.tighteningInPlace();
		}
		tc.mStrongClosure = mStrongClosure;
		tc.mTightClosure = mTightClosure = tc;
		return tc;
	}

	/** Compute the shortest path closure in-place, using the naive Floyd-Warshall algorithm. */
	protected void shortestPathClosureNaiv() {
		for (int k = 0; k < mSize; ++k) {
			for (int i = 0; i < mSize; ++i) {
				OctValue ik = get(i, k);
				for (int j = 0; j < mSize; ++j) {
					OctValue indirectRoute = ik.add(get(k, j));
					if (get(i, j).compareTo(indirectRoute) > 0) {
						set(i, j, indirectRoute);
					}
				}
			}
		}
	}

	/**
	 * Compute the shortest path closure in-place, using Singh's "Sparse Closure" algorithm
	 * (http://e-collection.library.ethz.ch/eserv/eth:8628/eth-8628-01.pdf).
	 * <p>
	 * This algorithm is based on Floyd-Warshall and runs on the full matrix.
	 * Finite matrix entries are indexed. Updates are computed using only the indexed entries.
	 */
	protected void shortestPathClosureFullSparse() {
		List<Integer> ck = null; // indices of finite elements in columns k and k^1
		List<Integer> rk = null; // indices of finite elements in rows k and k^1
		for (int k = 0; k < mSize; ++k) {
			ck = indexFiniteElementsInColumn(k);
			rk = indexFiniteElementsInRow(k);
			for (int i : ck) {
				OctValue ik = get(i, k);
				for (int j : rk) {
					OctValue kj = get(k, j);
					OctValue indirectRoute = ik.add(kj);
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
	 * @param k Column index
	 * @return Index of finite elements in column k (incoming edges of k)
	 */
	private List<Integer> indexFiniteElementsInColumn(int k) {
		List<Integer> index = new ArrayList<Integer>(mSize);
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
	 * @param k Row index
	 * @return Index of finite elements in row k (outgoing edges of k)
	 */
	private List<Integer> indexFiniteElementsInRow(int k) {
		List<Integer> index = new ArrayList<Integer>(mSize);
		for (int j = 0; j < mSize; ++j) {
			if (!get(k, j).isInfinity()) {
				index.add(j);
			}
		}
		return index;
	}

	/**
	 * Compute the shortest path closure in-place, using a sparse algorithm
	 * that iterates only the block lower triangular matrix.
	 * <p>
	 * This is a modification of {@link #shortestPathClosureFullSparse()}.
	 */
	protected void shortestPathClosureSparse() {
		List<Integer> ck = null; // indices of finite elements in columns k and k^1
		List<Integer> rk = null; // indices of finite elements in rows k and k^1
		for (int k = 0; k < mSize; ++k) {
			int kk = k ^ 1;
			if (k < kk) { // k is even => entered new 2x2 block
				ck = indexFiniteElementsInBlockColumn(k);
				rk = indexFiniteElementsInBlockRow(k);
			}
			for (int i : ck) {
				OctValue ik = get(i, k);
				OctValue ikk = get(i, kk);
				int maxCol = i | 1;
				for (int j : rk) {
					if (j > maxCol) {
						break;
					}
					OctValue kj = get(k, j);
					OctValue kkj = get(kk, j);
					OctValue indirectRoute = OctValue.min(ik.add(kj), ikk.add(kkj));
					if (get(i, j).compareTo(indirectRoute) > 0) {
						set(i, j, indirectRoute);
					}
				}
			}
		}
	}

	/**
	 * Indexes the the finite entries in a matrix block column.
	 * The index contains only the row indices of finite entries in the block column k/2.
	 * The index can not be used to determine whether the finite entry is in column k or column k+1.
	 * 
	 * @param k First column index of the block column (always an even number)
	 * @return Index of finite elements in block column k/2 (incoming edges of k and k+1)
	 */
	private List<Integer> indexFiniteElementsInBlockColumn(final int k) {
		List<Integer> index = new ArrayList<Integer>(mSize);
		int kk = k ^ 1;
		for (int i = 0; i < mSize; ++i) {
			if (!get(i, k).isInfinity() || !get(i, kk).isInfinity()) {
				index.add(i);
			}
		}
		return index;
	}

	/**
	 * Indexes the the finite entries in a matrix block row.
	 * The index contains only the column indices of finite entries in the block row k/2.
	 * The index can not be used to determine whether the finite entry is in row k or row k+1.
	 * 
	 * @param k First column index of the block row (always an even number)
	 * @return Index of finite elements in block row k/2 (outgoing edges of k and k+1)
	 */
	private List<Integer> indexFiniteElementsInBlockRow(final int k) {
		List<Integer> index = new ArrayList<Integer>(mSize);
		int kk = k ^ 1;
		for (int j = 0; j < mSize; ++j) {
			if (!get(k, j).isInfinity() || !get(kk, j).isInfinity()) {
				index.add(j);
			}
		}
		return index;
	}

	/**
	 * Computes the shortest path closure in-place, as in {@link #shortestPathClosureSparse()},
	 * while using only one primitive array instead of two java collections to represent the index.
	 */
	protected void shortestPathClosurePrimitiveSparse() {
		int[] rk = null; // indices of finite elements in rows k and k^1
		int[] ck = null; // indices of finite elements in columns k and k^1
		int indexLength = 0;
		for (int k = 0; k < mSize; ++k) {
			int kk = k ^ 1;
			if (k < kk) { // k is even => entered new 2x2 block
				rk = new int[mSize];
				ck = new int[mSize];
				indexLength = primitiveIndexFiniteElementsInBlockRowAndColumn(k, rk, ck);
			}
			for (int _i = 0; _i < indexLength; ++_i) {
				int i = ck[_i];
				OctValue ik = get(i, k);
				OctValue ikk = get(i, kk);
				int maxCol = i | 1;
				for (int _j = 0; _j < indexLength; ++_j) {
					int j = rk[_j];
					if (j > maxCol) {
						break;
					}
					OctValue kj = get(k, j);
					OctValue kkj = get(kk, j);
					OctValue indirectRoute = OctValue.min(ik.add(kj), ikk.add(kkj));
					if (get(i, j).compareTo(indirectRoute) > 0) {
						set(i, j, indirectRoute);
					}
				}
			}
		}
	}

	/**
	 * Indexes the the finite entries in block row k/2 and a block column k/2 at the same time.
	 * If the computed row index contains the value i, then there is a finite matrix entry at
	 * matrix index (i,k) or (i,k+1). If the computed column index contains the value i, then
	 * there is a finite matrix entry at matrix index (k,i), or (k+1,i).
	 * <p>
	 * The returned array has always the length {@link #getSize()}, but only the first n index entries are used.
	 * The length n of the index is the return value of this method.
	 * The row and column index always have the same length.
	 * 
	 * @param k First row/column index of the block row/column (always an even number)
	 * @param rowIndex
	 *            Index of finite elements in block row k/2 (outgoing edges of k and k+1).
	 *            This index is not completely sorted! The values 2i and 2i+1 are swapped.
	 * @param colIndex
	 *            Index of finite elements in block column k/2 (incoming edges of k and k+1)
	 * @return Actual length of the row/column indix
	 */
	private int primitiveIndexFiniteElementsInBlockRowAndColumn(
			final int k, final int[] rowIndex, final int[] colIndex) {
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
	 * Compute the shortest path closure in-place, using the closure algorithm of APRON (a library)
	 * as recalled by Singh (http://e-collection.library.ethz.ch/eserv/eth:8628/eth-8628-01.pdf).
	 * <p>
	 * This algorithm is based on Floyd-Warshall and iterates only the block lower triangular matrix.
	 */
	protected void shortestPathClosureApron() {
		for (int k = 0; k < mSize; ++k) {
			for (int i = 0; i < mSize; ++i) {
				OctValue ik = get(i, k);
				OctValue ikk = get(i, k ^ 1);
				int maxCol = i | 1;
				for (int j = 0; j <= maxCol; ++j) {
					OctValue kj = get(k, j);
					OctValue kkj = get(k ^ 1, j);
					OctValue indirectRoute = OctValue.min(ik.add(kj), ikk.add(kkj));
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
		// blocks on the diagonal (upper, lower bounds) won't change by strengthening
		// => iterate only 2x2 blocks that are _strictly_ below the main diagonal
		for (int i = 2; i < mSize; ++i) {
			OctValue ib = get(i, i ^ 1).half();
			int maxCol = (i - 2) | 1;
			for (int j = 0; j <= maxCol; ++j) {
				OctValue jb = get(j ^ 1, j).half();
				OctValue b = ib.add(jb);
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
			OctValue ib = get(i, i ^ 1).half().floor();
			int maxCol = i | 1;
			for (int j = 0; j <= maxCol; ++j) {
				OctValue jb = get(j ^ 1, j).half().floor();
				OctValue b = ib.add(jb);
				if (get(i, j).compareTo(b) > 0) {
					set(i, j, b);
				}
			}
		}
	}

	/**
	 * Checks for negative self loops in the graph represented by this adjacency matrix. Self loops are represented by
	 * this matrix' diagonal elements.
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
	 * Widens this octagon by another one.
	 * Constraints that would be loosened by a normal join are immediately removed by this widening operator.
	 * <p>
	 * This widening operator was presented by Mine (http://www-apr.lip6.fr/~mine/publi/article-mine-ast01.pdf).
	 * 
	 * @param n Other octagon
	 * @return This octagon, widened with {@code n}
	 */
	public OctMatrix widenSimple(final OctMatrix n) {
		return elementwiseOperation(n, (mij, nij) -> mij.compareTo(nij) >= 0 ? mij : OctValue.INFINITY);
	}

	// TODO document: stabilization depends on user-given threshold (stabilizes for threshold < inf)
	/**
	 * Widens this octagon by another one.
	 * Constraints that would be loosened by a normal join are loosened even more, using a binary exponential backoff.
	 * Constraints are removed, once the backoff reaches a given limit.
	 * 
	 * @param n Other octagon
	 * @param threshold TODO
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
				result = nij.half(); // there is no -inf => will always converge towards 0
			} else if (nij.signum() <= 0) {
				result = OctValue.ZERO;
			} else if (nij.compareTo(oneHalfEpsilon) <= 0) {
				result = epsilon;
			} else {
				result = nij.add(nij); // 2 * nij
			}
			return OctValue.min(result, threshold);
		});
		// OctValue result = nij;
		// if (result.compareTo(threshold) > 0) {
		// return OctValue.INFINITY;
		// }
		// int resultComp = result.compareTo(OctValue.ZERO);
		// if (resultComp > 0) {
		// result = OctValue.max(nij.add(nij), OctValue.ONE);
		// } else if (resultComp < 0) {
		// result = nij.half(); // there is no -inf => will always converge towards 0
		// result = result.compareTo(OctValue.MINUS_ONE) > 0 ? OctValue.ZERO : result;
		// } else {
		// result = nij; // == 0
		// }
		// return result;
	}

	public interface WideningStepSupplier {
		public OctValue nextWideningStep(final OctValue val);
	}

	public OctMatrix widenStepwise(OctMatrix n, WideningStepSupplier stepSupplier) {
		return elementwiseOperation(n, (mij, nij) -> {
			if (mij.compareTo(nij) >= 0) {
				return mij;
			} else {
				return stepSupplier.nextWideningStep(nij);
			}
		});
	}

	public OctMatrix addVariables(int count) {
		if (count < 0) {
			throw new IllegalArgumentException("Cannot add " + count + " variables.");
		} else if (count == 0) {
			return this;
		}
		OctMatrix n = new OctMatrix(mSize + (2 * count));
		System.arraycopy(mElements, 0, n.mElements, 0, mElements.length);
		Arrays.fill(n.mElements, this.mElements.length, n.mElements.length, OctValue.INFINITY);
		// cached closures are of different size and cannot be (directly) reused
		return n;
	}

	public OctMatrix removeVariable(int v) {
		return removeVariables(Collections.singleton(v));
	}

	public OctMatrix removeVariables(final Set<Integer> vars) {
		if (areVariablesLast(vars)) {
			return removeLastVariables(vars.size()); // note: sets cannot contain duplicates
		} else {
			return removeArbitraryVariables(vars);
		}
	}

	private boolean areVariablesLast(final Set<Integer> vars) {
		List<Integer> varsDescending = new ArrayList<>(vars);
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

	public OctMatrix removeLastVariables(final int count) {
		if (count > variables()) {
			throw new IllegalArgumentException("Cannot remove more variables than exist.");
		}
		OctMatrix n = new OctMatrix(mSize - (2 * count));
		System.arraycopy(mElements, 0, n.mElements, 0, n.mElements.length);
		// cached closures are of different size and cannot be (directly) reused
		return n;
	}

	public OctMatrix removeArbitraryVariables(final Set<Integer> vars) {
		OctMatrix n = new OctMatrix(mSize - (2 * vars.size())); // note: sets cannot contain duplicates
		int in = 0;
		for (int i = 0; i < mSize; ++i) {
			if (vars.contains(i / 2)) {
				// 2x2 block row shall be removed => continue in next 2x2 block row
				++i;
				continue;
			}
			int maxCol = i | 1;
			for (int j = 0; j <= maxCol; ++j) {
				if (vars.contains(j / 2)) {
					// 2x2 block column shall be removed => continue in next 2x2 block
					++j;
					continue;
				}
				n.mElements[in++] = get(i, j);
			}
		}
		// cached closures are of different size and cannot be (directly) reused
		return n;
	}

	// TODO document
	// - note that information is lost. Strong Closure on this and source in advance can reduce loss.
	// - source must be different from target (= this)
	protected void copySelection(
			final OctMatrix source, final BidirectionalMap<Integer, Integer> mapTargetVarToSourceVar) {

		BidirectionalMap<Integer, Integer> mapSourceVarToTargetVar = mapTargetVarToSourceVar.inverse();

		if (source.mElements == mElements) {
			for (final Map.Entry<Integer, Integer> entry : mapSourceVarToTargetVar.entrySet()) {
				if (!entry.getKey().equals(entry.getValue())) {
					throw new UnsupportedOperationException("Cannot overwrite in place");
				}
			}
			return;
		}
		for (final Map.Entry<Integer, Integer> entry : mapSourceVarToTargetVar.entrySet()) {
			int sourceVar = entry.getKey();
			int targetVar = entry.getValue();
			// Copy columns. Rows are copied by coherence.
			for (int targetOther = 0; targetOther < variables(); ++targetOther) {
				Integer row = mapTargetVarToSourceVar.get(targetOther);
				if (row == null) {
					setBlock(targetOther, targetVar, OctValue.INFINITY);
				} else {
					copyBlock(targetOther, targetVar, /* := */ source, row, sourceVar);
				}
			}
		}
	}

	// TODO document
	// - selectedSourceVars should not contain duplicates
	// - iteration order matters
	public OctMatrix appendSelection(final OctMatrix source, final Collection<Integer> selectedSourceVars) {
		OctMatrix m = this.addVariables(selectedSourceVars.size());
		BidirectionalMap<Integer, Integer> mapTargetVarToSourceVar = new BidirectionalMap<>();
		for (final Integer sourceVar : selectedSourceVars) {
			int targetVar = mapTargetVarToSourceVar.size() + variables();
			Integer prevValue = mapTargetVarToSourceVar.put(targetVar, sourceVar);
			assert prevValue == null : "Selection contained duplicate: " + sourceVar;
		}
		m.copySelection(source, mapTargetVarToSourceVar);
		return m;
	}

	protected void copyBlock(int targetBRow, int targetBCol, final OctMatrix source, int sourceBRow, int sourceBCol) {
		targetBRow *= 2;
		targetBCol *= 2;
		sourceBRow *= 2;
		sourceBCol *= 2;
		for (int j = 0; j < 2; ++j) {
			for (int i = 0; i < 2; ++i) {
				set(targetBRow + i, targetBCol + j, source.get(sourceBRow + i, sourceBCol + j));
			}
		}
	}

	protected void setBlock(int bRow, int bCol, OctValue v) {
		bRow *= 2;
		bCol *= 2;
		for (int j = 0; j < 2; ++j) {
			for (int i = 0; i < 2; ++i) {
				set(bRow + i, bCol + j, v);
			}
		}
	}

	/**
	 * Assigns one variable to another variable in this matrix. {@code x := y;}
	 * <p>
	 * This method is exact. No precision is lost. Closure in advance is not necessary. Already closed matrices remain
	 * closed.
	 * 
	 * @param targetVar
	 *            variable which will be changed
	 * @param sourceVar
	 *            variable which will be copied
	 */
	protected void assignVarCopy(int targetVar, int sourceVar) {
		if (targetVar == sourceVar) {
			return;
		}
		boolean wasStronglyClosed = mStrongClosure == this;
		boolean wasTightlyClosed = mTightClosure == this;

		int t2 = targetVar * 2;
		int s2 = sourceVar * 2;
		int t21 = t2 + 1;
		int s21 = s2 + 1;

		// "x == y" cannot be detected when imprecise "x + x <= 4" is copied
		minimizeDiagonalElement(s2);
		minimizeDiagonalElement(s2 + 1);

		// copy (block lower) block-row (including diagonal block)
		int length = Math.min(s2, t2) + 2;
		System.arraycopy(mElements, indexOfLower(s2, 0), mElements, indexOfLower(t2, 0), length);
		System.arraycopy(mElements, indexOfLower(s21, 0), mElements, indexOfLower(t21, 0), length);

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
			// tightly closed => all variables have integral values => copied variable had integral value
			mTightClosure = this;
		}
	}

	/**
	 * Negates a variable. {@code x := -x;}
	 * <p>
	 * This method is exact. No precision is lost. Closure in advance is not necessary. Already closed matrices remain
	 * closed.
	 * 
	 * @param targetVar
	 *            variable which will be negated
	 */
	protected void negateVar(int targetVar) {
		int t2 = targetVar * 2;
		int t21 = t2 + 1;

		// swap (block lower) sub-rows of block-row (including diagonal block)
		int t2RowStart = indexOf(t2, 0);
		int t21RowStart = indexOf(t21, 0);
		int length = t2 + 2;
		OctValue[] tmpRow = new OctValue[length];
		System.arraycopy(mElements, t2RowStart, tmpRow, 0, length); // tmp row := upper row
		System.arraycopy(mElements, t21RowStart, mElements, t2RowStart, length); // upper row := lower row
		System.arraycopy(tmpRow, 0, mElements, t21RowStart, length); // lower row := tmp row

		// swap (block lower) sub-columns of block-column (including diagonal block)
		for (int row = t2; row < mSize; ++row) {
			int left = indexOfLower(row, t2);
			int right = left + 1;
			OctValue tmpVal = mElements[left];
			mElements[left] = mElements[right];
			mElements[right] = tmpVal;
		}

		if (mStrongClosure != this) {
			mStrongClosure = null;
		}
		if (mTightClosure != this) {
			mTightClosure = null;
		}
	}

	/**
	 * Adds a constant to a variable. {@code v := v + c;} The constant may also be negative.
	 * <p>
	 * This method is exact. No precision is lost. Closure in advance is not necessary. Already closed matrices remain
	 * closed.
	 * 
	 * @param targetVar
	 *            variable to be incremented
	 * @param constant
	 *            summand
	 */
	protected void incrementVar(final int targetVar, final OctValue constant) {
		int t2 = targetVar * 2;
		int t21 = t2 + 1;

		// increment block-column, block-row is incremented by coherence
		for (int row = 0; row < mSize; ++row) {
			if (row / 2 == targetVar) {
				continue; // block (v, v) is processed after this loop
			}
			int iT2 = indexOf(row, t2); // left sub-column of block-column
			int iT21 = indexOf(row, t21); // right ...
			mElements[iT2] = mElements[iT2].add(constant); // (v + c) − ? ≤ ? <=> v − ? ≤ ?
			mElements[iT21] = mElements[iT21].subtract(constant); // −(v + c) − ? ≤ ? <=> −v − ? ≤ ? − c
		}

		OctValue doubleConstant = constant.add(constant);
		int iUpperBound2 = indexOf(t21, t2);
		int iLowerBound2 = indexOf(t2, t21);
		mElements[iUpperBound2] = mElements[iUpperBound2].add(doubleConstant);
		mElements[iLowerBound2] = mElements[iLowerBound2].subtract(doubleConstant);

		if (mStrongClosure != this) {
			mStrongClosure = null;
		}
		if (mTightClosure != this) {
			assert constant.isInfinity() || NumUtil.isIntegral(constant.getValue()) : "int incremented by real";
			mTightClosure = null;
		}
	}

	protected void assignVarConstant(final int targetVar, final OctValue constant) {
		havocVar(targetVar);
		int t2 = targetVar * 2;
		int t21 = t2 + 1;
		OctValue doubleConstant = constant.add(constant);
		set(t2, t21, doubleConstant.negate());
		set(t21, t2, doubleConstant);
		// cached closures were already reset by "set"
	}

	protected void assumeVarConstant(final int targetVar, final OctValue constant) {
		int t2 = targetVar * 2;
		int t21 = t2 + 1;
		OctValue doubleConstant = constant.add(constant);
		setMin(t2, t21, doubleConstant.negate());
		setMin(t21, t2, doubleConstant);
		// cached closures were already reset by "set"
	}

	protected void assignVarInterval(final int targetVar, final OctValue min, final OctValue max) {
		havocVar(targetVar);
		int t2 = targetVar * 2;
		int t21 = t2 + 1;
		set(t2, t21, min.add(min).negateIfNotInfinity());
		set(t21, t2, max.add(max));
		// cached closures were already reset by "set"
	}

	protected void assumeVarInterval(final int targetVar, final OctValue min, final OctValue max) {
		int t2 = targetVar * 2;
		int t21 = t2 + 1;
		setMin(t2, t21, min.add(min).negateIfNotInfinity());
		setMin(t21, t2, max.add(max));
		// cached closures were already reset by "set"
	}

	// var1 + var2 <= constant
	protected void assumeVarRelationLeConstant(int var1, final boolean var1Negate, int var2, final boolean var2Negate,
			OctValue constant) {
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
		int t2 = targetVar * 2;
		int t21 = t2 + 1;

		// Set block-column. Block-row is set by coherence.
		for (int row = 0; row < mSize; ++row) {
			mElements[indexOf(row, t2)] = mElements[indexOf(row, t21)] = OctValue.INFINITY;
		}
		set(t2, t2, OctValue.ZERO);
		set(t21, t21, OctValue.ZERO);

		// cached closures were already reset by "set"
	}

	public double infinityPercentageInBlockLowerHalf() {
		if (mElements.length == 0) {
			return Double.NaN;
		}
		int infCounter = 0;
		for (OctValue v : mElements) {
			if (v.isInfinity()) {
				++infCounter;
			}
		}
		return infCounter / (double) mElements.length;
	}

	public List<Term> getTerm(final Script script, final Term[] vars) {
		final List<Term> rtr = new ArrayList<Term>(variables() * variables());
		for (int row = 0; row < 2 * variables(); ++row) {
			final Term rowVar = selectVar(script, row, vars);
			// iterate only block lower triangular matrix (skip coherent upper part)
			for (int col = 0; col < (row / 2 + 1) * 2; ++col) {
				final OctValue entry = get(row, col);
				if (col == row) {
					if (entry.signum() < 0) {
						return Collections.singletonList(script.term("false")); // constraint of the form (0 <= -1)
					} else {
						continue; // constraint of the form (0 <= 1)
					}
				}
				final Term colVar = selectVar(script, col, vars);
				rtr.add(createBoundedDiffTerm(script, colVar, rowVar, entry));
			}
		}
		return rtr;
	}

	// returns variable in positive or negative form, depending on row or column
	private Term selectVar(final Script script, final int rowCol, final Term[] vars) {
		Term posNegVar = vars[rowCol / 2];
		if (rowCol % 2 == 1) {
			return script.term("-", posNegVar);
		}
		return posNegVar;
	}

	// returns minuend - subtrahend <= bound
	private Term createBoundedDiffTerm(final Script script, Term minuend, Term subtrahend, final OctValue bound) {
		if (bound.isInfinity()) {
			return script.term("true");
		}
		final Term tBound;
		boolean minuendIsInt = TypeUtil.isIntTerm(minuend);
		boolean subtrahendIsInt = TypeUtil.isIntTerm(subtrahend);
		if (minuendIsInt && subtrahendIsInt) {
			tBound = script.numeral(bound.getValue().round(new MathContext(0, RoundingMode.FLOOR)).toBigIntegerExact());
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

	public String toStringHalf() {
		final StringBuilder sb = new StringBuilder();
		int n = 2; // input of integer sequence floor(n^2 / 2 -1)
		int rowEnd = 1; // index of last element in current row (= output of integer sequence)
		for (int i = 0; i < mElements.length; ++i) {
			sb.append(mElements[i]);
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
