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
 * Matrix for octagons (as presented by Antoine Mine).
 * <p>
 * 
 * TODO More documentation Stores entries for variables +v1, -v1, ..., +vn, -vn Variables (names, type, ...) aren't
 * stored Matrix is divided into 2x2 blocks Different matrices, same octagon -> closures
 * 
 * This class ensures coherence (as seen in the following ASCII art).
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
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class OctMatrix {

	public final static OctMatrix NEW = new OctMatrix(0);

	private final static Consumer<OctMatrix> sDefaultShortestPathClosure = OctMatrix::shortestPathClosurePrimitiveSparse;
	// private final static Consumer<OctMatrix> sDefaultShortestPathClosure = m -> {
	// if (m.mSize <= 0) {
	// return;
	// }
	// String s = m.toStringLower();
	// BufferedWriter bw;
	// try {
	// bw = new BufferedWriter(new FileWriter(makeFilename()), s.length() * 2);
	// try {
	// bw.write(s);
	// } finally {
	// bw.close();
	// }
	// } catch (IOException e) {
	// throw new AssertionError("Could not write benchmark file.", e);
	// }
	// m.shortestPathClosurePrimitiveSparse();
	// };
	// private static String makeFilename() {
	// int i;
	// synchronized (OctMatrix.class) {
	// i = ++sFileNameCounter;
	// }
	// return "/tmp/closureBenchmarkSvcomp/" + String.format("%08d", i);
	// }
	// private static volatile int sFileNameCounter = 0;

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

	private OctMatrix mStrongClosure;
	private OctMatrix mTightClosure;

	public OctMatrix copy() {
		OctMatrix copy = new OctMatrix(mSize);
		System.arraycopy(this.mElements, 0, copy.mElements, 0, mElements.length);
		copy.mStrongClosure = (mStrongClosure == this) ? copy : mStrongClosure;
		copy.mTightClosure = (mTightClosure == this) ? copy : mTightClosure;
		return copy;
	}

	public static OctMatrix parseBlockLowerTriangular(String m) {
		m = m.trim();
		String[] elements = m.length() > 0 ? m.split("\\s+") : new String[0];
		int size = (int) (Math.sqrt(2 * elements.length + 1) - 1);
		if (size % 2 != 0) {
			throw new IllegalArgumentException(
					"Number of elements does not match any 2x2 block lower triangular matrix.");
		}
		OctMatrix oct = new OctMatrix(size);
		for (int i = 0; i < elements.length; ++i) {
			oct.mElements[i] = OctValue.parse(elements[i]);
		}
		return oct;
	}

	public static OctMatrix random(int variables) {
		return random(variables, Math.random());
	}

	/**
	 * @param infProbability
	 *            probability that an element will be infinity (0 = never, 1 = always)
	 */
	public static OctMatrix random(int variables, double infProbability) {
		OctMatrix m = new OctMatrix(variables * 2);
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

	protected OctMatrix(int size) {
		mSize = size;
		mElements = new OctValue[size * size / 2 + size];
	}

	protected void fillInPlace(OctValue fill) {
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
	 * Returns the number of variables, stored by this octagon. Each variable corresponds to two rows and two columns of
	 * the octagon matrix.
	 * 
	 * @return number of variables in this octagon
	 */
	public int variables() {
		return mSize / 2;
	}

	public OctValue get(int row, int col) {
		return mElements[indexOf(row, col)];
	}

	protected void set(int row, int col, OctValue value) {
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
	 * @param row
	 *            row of the matrix entry
	 * @param col
	 *            column of the matrix entry
	 * @param newValue
	 *            new value of the matrix entry (must be smaller than the old value to have an effect)
	 */
	protected void setMin(int row, int col, OctValue newValue) {
		assert newValue != null : "null is not a valid matrix element.";
		mStrongClosure = mTightClosure = null;
		int index = indexOf(row, col);
		if (newValue.compareTo(mElements[index]) < 0) {
			mElements[index] = newValue;
			mStrongClosure = mTightClosure = null;
		}
	}

	/**
	 * Set positive values on the main diagonal to zero. Negative values are kept, since they denote that this octagon
	 * is \bot. When encountering an negative value, this method exits early => positive values may remain on the
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

	private boolean minimizeDiagonalElement(int i) {
		int ii = indexOfLower(i, i);
		int sig = mElements[ii].signum();
		if (sig > 0) {
			mElements[ii] = OctValue.ZERO;
			// no need to reset cached closures -- diagonal is always minimized on closure computation
			return false;
		}
		return sig < 0;
	}

	private int indexOf(int row, int col) {
		assert row < mSize && col < mSize : row + "," + col + " is not an index for matrix of size " + mSize + ".";
		if (row < col) {
			return indexOfLower(col ^ 1, row ^ 1);
		}
		return indexOfLower(row, col);
	}

	private int indexOfLower(int row, int col) {
		return col + (row + 1) * (row + 1) / 2;
	}

	public OctMatrix elementwiseOperation(OctMatrix other, BiFunction<OctValue, OctValue, OctValue> operator) {
		checkCompatibility(other);
		OctMatrix result = new OctMatrix(mSize);
		for (int i = 0; i < mElements.length; ++i) {
			result.mElements[i] = operator.apply(mElements[i], other.mElements[i]);
		}
		return result;
	}

	public boolean elementwiseRelation(OctMatrix other, BiFunction<OctValue, OctValue, Boolean> relation) {
		checkCompatibility(other);
		for (int i = 0; i < mElements.length; ++i) {
			if (!relation.apply(mElements[i], other.mElements[i])) {
				return false;
			}
		}
		return true;
	}

	private void checkCompatibility(OctMatrix other) {
		if (other.mSize != mSize) {
			throw new IllegalArgumentException("Incompatible matrices");
		}
	}

	public OctMatrix add(OctMatrix other) {
		return elementwiseOperation(other, OctValue::add);
	}

	public static OctMatrix min(OctMatrix a, OctMatrix b) {
		return a.elementwiseOperation(b, OctValue::min);
	}

	public static OctMatrix max(OctMatrix a, OctMatrix b) {
		return a.elementwiseOperation(b, OctValue::max);
		// TODO set cached closure of result:
		// a and b are closed ==> max(a,b) are closed
	}

	// TODO document: Different matrices may represent the same octagon.
	public boolean isEqualTo(OctMatrix other) {
		if (this == other) {
			return true;
		}
		return elementwiseRelation(other, (x, y) -> x.compareTo(y) == 0);
	}

	public boolean isEqualToPermutation(OctMatrix permutation, int[] mapThisVarIndexToPermVarIndex) {
		for (int bRow = 0; bRow < variables(); ++bRow) {
			// compare only block lower triangular part (upper part is coherent)
			for (int bCol = 0; bCol <= bRow; ++bCol) {
				int permBRow = mapThisVarIndexToPermVarIndex[bRow];
				int permBCol = mapThisVarIndexToPermVarIndex[bCol];
				if (!isBlockEqualTo(bRow, bCol, permutation, permBRow, permBCol)) {
					return false;
				}
			}
		}
		return true;
	}

	public boolean isBlockEqualTo(int bRow, int bCol, OctMatrix other, int otherBRow, int otherBCol) {
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

	// note: "not less-equal than" does not necessarily mean "greater than". OctMatrices are only partial ordered!
	public boolean isLessEqualThan(OctMatrix other) {
		return elementwiseRelation(other, (x, y) -> x.compareTo(y) <= 0);
	}

	// TODO document: cached closure is the original object. Do not modify!
	public OctMatrix cachedStrongClosure() {
		if (mStrongClosure != null) {
			return mStrongClosure;
		}
		return strongClosure(sDefaultShortestPathClosure);
	}

	public OctMatrix strongClosure(Consumer<OctMatrix> shortestPathClosureAlgorithm) {
		OctMatrix sc = copy();
		boolean isObviouslyBottom = sc.minimizeDiagonal();
		if (!isObviouslyBottom) {
			shortestPathClosureAlgorithm.accept(sc);
			sc.strengtheningInPlace();
		}
		sc.mStrongClosure = mStrongClosure = sc;
		sc.mTightClosure = mTightClosure;
		return sc;
	}

	// TODO document: cached closure is the original object. Do not modify!
	public OctMatrix cachedTightClosure() {
		if (mTightClosure != null) {
			return mTightClosure;
		}
		return tightClosure(sDefaultShortestPathClosure);
	}

	public boolean hasCachedStrongClosure() {
		return mStrongClosure != null;
	}

	public boolean hasCachedTightClosure() {
		return mTightClosure != null;
	}

	public OctMatrix tightClosurePrimitiveSparse() {
		return tightClosure(OctMatrix::shortestPathClosurePrimitiveSparse);
	}

	public OctMatrix tightClosure(Consumer<OctMatrix> shortestPathClosureAlgorithm) {
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

	// incoming edges of k
	private List<Integer> indexFiniteElementsInColumn(int k) {
		List<Integer> index = new ArrayList<Integer>(mSize);
		for (int i = 0; i < mSize; ++i) {
			if (!get(i, k).isInfinity()) {
				index.add(i);
			}
		}
		return index;
	}

	// outgoing edges of k
	private List<Integer> indexFiniteElementsInRow(int k) {
		List<Integer> index = new ArrayList<Integer>(mSize);
		for (int j = 0; j < mSize; ++j) {
			if (!get(k, j).isInfinity()) {
				index.add(j);
			}
		}
		return index;
	}

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

	private List<Integer> indexFiniteElementsInBlockColumn(int k) {
		List<Integer> index = new ArrayList<Integer>(mSize);
		int kk = k ^ 1;
		for (int i = 0; i < mSize; ++i) {
			if (!get(i, k).isInfinity() || !get(i, kk).isInfinity()) {
				index.add(i);
			}
		}
		return index;
	}

	private List<Integer> indexFiniteElementsInBlockRow(int k) {
		List<Integer> index = new ArrayList<Integer>(mSize);
		int kk = k ^ 1;
		for (int j = 0; j < mSize; ++j) {
			if (!get(k, j).isInfinity() || !get(kk, j).isInfinity()) {
				index.add(j);
			}
		}
		return index;
	}

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

	// note: rowIndex is not sorted. Block elements are swapped.
	private int primitiveIndexFiniteElementsInBlockRowAndColumn(int k, int[] rowIndex, int[] colIndex) {
		int indexLength = 0;
		int kk = k ^ 1;
		for (int i = 0; i < mSize; ++i) {
			if (!get(i, k).isInfinity() || !get(i, kk).isInfinity()) {
				colIndex[indexLength] = i;
				rowIndex[indexLength] = i ^ 1;
				++indexLength;
			}
		}
		return indexLength;
	}

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

	public OctMatrix widenSimple(OctMatrix n) {
		return elementwiseOperation(n, (mij, nij) -> mij.compareTo(nij) >= 0 ? mij : OctValue.INFINITY);
	}

	// TODO document: stabilization depends on user-given threshold (stabilizes for threshold < inf)
	public OctMatrix widenExponential(OctMatrix n, OctValue threshold) {
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
		public OctValue nextWideningStep(OctValue v);
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

	public OctMatrix removeVariables(Set<Integer> vars) {
		if (areVariablesLast(vars)) {
			return removeLastVariables(vars.size()); // note: sets cannot contain duplicates
		} else {
			return removeArbitraryVariables(vars);
		}
	}

	private boolean areVariablesLast(Set<Integer> vars) {
		List<Integer> varsDescending = new ArrayList<>(vars);
		Collections.sort(varsDescending);
		int vPrev = variables();
		for (int v : varsDescending) {
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

	public OctMatrix removeLastVariables(int count) {
		if (count > variables()) {
			throw new IllegalArgumentException("Cannot remove more variables than exist.");
		}
		OctMatrix n = new OctMatrix(mSize - (2 * count));
		System.arraycopy(mElements, 0, n.mElements, 0, n.mElements.length);
		// cached closures are of different size and cannot be (directly) reused
		return n;
	}

	public OctMatrix removeArbitraryVariables(Set<Integer> vars) {
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
	protected void copySelection(OctMatrix source, BidirectionalMap<Integer, Integer> mapTargetVarToSourceVar) {

		BidirectionalMap<Integer, Integer> mapSourceVarToTargetVar = mapTargetVarToSourceVar.inverse();

		if (source.mElements == mElements) {
			for (Map.Entry<Integer, Integer> entry : mapSourceVarToTargetVar.entrySet()) {
				if (!entry.getKey().equals(entry.getValue())) {
					throw new UnsupportedOperationException("Cannot overwrite in place");
				}
			}
			return;
		}
		for (Map.Entry<Integer, Integer> entry : mapSourceVarToTargetVar.entrySet()) {
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
	public OctMatrix appendSelection(OctMatrix source, Collection<Integer> selectedSourceVars) {
		OctMatrix m = this.addVariables(selectedSourceVars.size());
		BidirectionalMap<Integer, Integer> mapTargetVarToSourceVar = new BidirectionalMap<>();
		for (Integer sourceVar : selectedSourceVars) {
			int targetVar = mapTargetVarToSourceVar.size() + variables();
			Integer prevValue = mapTargetVarToSourceVar.put(targetVar, sourceVar);
			assert prevValue == null : "Selection contained duplicate: " + sourceVar;
		}
		m.copySelection(source, mapTargetVarToSourceVar);
		return m;
	}

	protected void copyBlock(int targetBRow, int targetBCol, OctMatrix source, int sourceBRow, int sourceBCol) {
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
	protected void incrementVar(int targetVar, OctValue constant) {
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

	protected void assignVarConstant(int targetVar, OctValue constant) {
		havocVar(targetVar);
		int t2 = targetVar * 2;
		int t21 = t2 + 1;
		OctValue doubleConstant = constant.add(constant);
		set(t2, t21, doubleConstant.negate());
		set(t21, t2, doubleConstant);
		// cached closures were already reset by "set"
	}

	protected void assumeVarConstant(int targetVar, OctValue constant) {
		int t2 = targetVar * 2;
		int t21 = t2 + 1;
		OctValue doubleConstant = constant.add(constant);
		setMin(t2, t21, doubleConstant.negate());
		setMin(t21, t2, doubleConstant);
		// cached closures were already reset by "set"
	}

	protected void assignVarInterval(int targetVar, OctValue min, OctValue max) {
		havocVar(targetVar);
		int t2 = targetVar * 2;
		int t21 = t2 + 1;
		set(t2, t21, min.add(min).negateIfNotInfinity());
		set(t21, t2, max.add(max));
		// cached closures were already reset by "set"
	}

	protected void assumeVarInterval(int targetVar, OctValue min, OctValue max) {
		int t2 = targetVar * 2;
		int t21 = t2 + 1;
		setMin(t2, t21, min.add(min).negateIfNotInfinity());
		setMin(t21, t2, max.add(max));
		// cached closures were already reset by "set"
	}

	// var1 + var2 <= constant
	protected void assumeVarRelationLeConstant(int var1, boolean var1Negate, int var2, boolean var2Negate,
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

	protected void havocVar(int targetVar) {
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

	// only kept for comparison -- do not use regularly
	@Deprecated
	protected void mineAssignRelational(int targetVar, int sourceVar, OctValue addConstant) {
		OctValue addConstantNegated = addConstant.negate();
		int v2 = targetVar * 2;
		if (targetVar == sourceVar) {
			// update column (row is updated by coherence)
			for (int i = 0; i < mSize; ++i) {
				int beta = 0;
				if (i == v2) {
					beta = -1;
				} else if (i == v2 + 1) {
					beta = 1;
				}
				for (int j = v2; j < v2 + 2; ++j) {
					int alpha = (j == v2) ? 1 : -1;
					int factor = alpha + beta;
					if (factor == 1) {
						set(i, j, get(i, j).add(addConstant));
					} else if (factor == -1) {
						set(i, j, get(i, j).add(addConstantNegated));
					}
				}
			}
		} else {
			shortestPathClosureNaiv();
			strengtheningInPlace();
			havocVar(targetVar);
			int ov2 = sourceVar * 2;
			set(ov2, v2, addConstant); // also sets entry (v2 + 1, ov2 + 1) by coherence
			set(v2, ov2, addConstantNegated); // also sets entry (ov2 + 1, v2 + 1) by coherence
		}
		mStrongClosure = mTightClosure = null;
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

	public List<Term> getTerm(Script script, Term[] vars) {
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
	private Term selectVar(Script script, int rowCol, Term[] vars) {
		Term posNegVar = vars[rowCol / 2];
		if (rowCol % 2 == 1) {
			return script.term("-", posNegVar);
		}
		return posNegVar;
	}

	// returns minuend - subtrahend <= bound
	private Term createBoundedDiffTerm(Script script, Term minuend, Term subtrahend, OctValue bound) {
		if (bound.isInfinity()) {
			return script.term("true");
		}
		Term tBound;
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
		StringBuilder sb = new StringBuilder();
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
		StringBuilder sb = new StringBuilder();
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
