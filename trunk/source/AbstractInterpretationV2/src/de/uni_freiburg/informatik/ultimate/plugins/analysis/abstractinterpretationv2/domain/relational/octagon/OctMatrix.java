package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.Arrays;
import java.util.function.BiFunction;
import java.util.function.Function;

/**
 * Matrix for octagons (as presented by Antoine Mine).
 * <p>
 * 
 * TODO More documentation
 * TODO Stores entries for variables +v1, -v1, ..., +vn, -vn
 * TODO Variables (names, type, ...) aren't stored
 * TODO Matrix is divided into 2x2 blocks
 * TODO Different matrices, same octagon -> closures
 * 
 * This class ensures coherence (as seen in the following ASCII art).
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

	/**
	 * Size of this matrix (size = #rows = #columns).
	 * Size is always an even number.
	 */
	private final int mSize;
	
	/**
	 * Stores the elements of this matrix.
	 * <p> 
	 * Some elements are neglected because they are coherent to other elements
	 * (see documentation of this class). The stored elements and their
	 * indices are shown in the following ASCII art.
	 * <pre>
	 *     0 1 . . . .    legend
	 *     2 3 . . . .    -----------------
	 *     4 5 6 7 . .    .      not stored
	 *     8 9 # # . .    0-9 #  stored    
	 *     # # # # # #
	 *     # # # # # #    m_0,0 is top left
	 * </pre>
	 * The matrix is divided into 2x2 blocks. Every block that contains
	 * at least one element from the block lower triangular matrix is completely
	 * stored. Elements are stored row-wise from top to bottom, left to right.
	 * 
	 * @see #indexOf(int, int)
	 */
	private final OctValue[] mElements;

	@Override
	public OctMatrix clone() {
		OctMatrix clone = new OctMatrix(mSize);
		System.arraycopy(this.mElements, 0, clone.mElements, 0, mElements.length);
		return clone;
	}
	
	public static OctMatrix top(int variables) {
		OctMatrix top = new OctMatrix(variables * 2);
		Arrays.fill(top.mElements, OctValue.INFINITY);
		top.setMainDiagonal(OctValue.ZERO);
		return top;
	}

	public static OctMatrix parseBlockLowerTriangular(String m) {
		String[] elements = m.trim().split("\\s+");
		int size = (int) (Math.sqrt(2 * elements.length + 1) - 1);
		if (size % 2 != 0) {
			throw new IllegalArgumentException("Number of elements does not match any 2x2 block lower triangular matrix.");
		}
		OctMatrix oct = new OctMatrix(size);
		for (int i = 0; i < elements.length; ++i) {
			oct.mElements[i] = OctValue.parse(elements[i]);
		}
		return oct;
	}
	
	private OctMatrix(int size) {
		mSize = size;
		mElements = new OctValue[size * size / 2 + size];
	}
	
	public int getSize() {
		return mSize;
	}
	
	public int variables() {
		return mSize / 2;
	}
	
	public OctValue get(int row, int col) {
		return mElements[indexOf(row, col)];
	}
	
	protected void set(int row, int col, OctValue value) {
		if(value == null) {
			throw new IllegalArgumentException("null is not a valid matrix element.");
		}
		mElements[indexOf(row, col)] = value;
	}
	
	protected void setMainDiagonal(OctValue value) {
		for (int i = 0; i < mSize; ++i) {
			mElements[indexOfLower(i, i)] = value;
		}
	}

	private int indexOf(int row, int col) {
		if (row >= mSize || col >= mSize) {
			throw new IndexOutOfBoundsException(row + "," + col + " is not an index for matrix of size " + mSize + ".");
		} else if (row < col) {
			return indexOfLower(col ^ 1, row ^ 1);
		}
		return indexOfLower(row, col);
	}

	private int indexOfLower(int row, int col) {
		return col + (row + 1) * (row + 1) / 2;
	}

	public OctMatrix elementwiseOperation(OctMatrix other, BiFunction<OctValue, OctValue, OctValue> operator) {
		if (other.mSize != mSize) {
			throw new IllegalArgumentException("Incompatible matrices");
		}
		OctMatrix result = new OctMatrix(mSize);
		for (int i = 0; i < mElements.length; ++i) {
			result.mElements[i] = operator.apply(mElements[i], other.mElements[i]);
		}
		return result;
	}
	
	public boolean elementwiseRelation(OctMatrix other, BiFunction<OctValue, OctValue, Boolean> relation) {
		if (other.mSize != mSize)
			throw new IllegalArgumentException("Incompatible matrices");
		for (int i = 0; i < mElements.length; ++i) {
			if (!relation.apply(mElements[i], other.mElements[i])) {
				return false;
			}
		}
		return true;
	}

	public OctMatrix add(OctMatrix other) {
		return elementwiseOperation(other, OctValue::add);
	}
	
	public static OctMatrix min(OctMatrix a, OctMatrix b) {
		return a.elementwiseOperation(b, OctValue::min);
	}
	
	public static OctMatrix max(OctMatrix a, OctMatrix b) {
		return a.elementwiseOperation(b, OctValue::max);
	}

	// TODO document: Different matrices may represent the same octagon.
	public boolean isEqualTo(OctMatrix other) {
		return elementwiseRelation(other, (x, y) -> x.compareTo(y) == 0);
	}
	
	public boolean isLessEqualThan(OctMatrix other) {
		return elementwiseRelation(other, (x, y) -> x.compareTo(y) <= 0);		
	}
	
	public OctMatrix strongClosure() {
		OctMatrix sc = this.clone();
		sc.shortestPathClosureInPlace();
		sc.strengtheningInPlace();
		return sc;
	}
	
	public OctMatrix tightClosure() {
		OctMatrix tc = this.clone();
		tc.shortestPathClosureInPlace();
		tc.tighteningInPlace();
		return tc;
	}

	private void shortestPathClosureInPlace() {
		setMainDiagonal(OctValue.ZERO);
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

	private void strengtheningInPlace() {
		// blocks on the diagonal (upper, lower bounds) won't change by strengthening
		// => iterate only 2x2 blocks that are _strictly_ below the main diagonal
		for (int i = 2; i < mSize; ++i) {
			int maxCol = (i - 2) | 1;
			OctValue ib = get(i, i^1).half();
			for (int j = 0; j <= maxCol; ++j) {
				OctValue jb = get(j^1, j).half();
				OctValue b = ib.add(jb);
				if (get(i, j).compareTo(b) > 0) {
					set(i, j, b);
				}
			}
		}		
	}

	private void tighteningInPlace() {
		for (int i = 0; i < mSize; ++i) {
			int maxCol = i | 1;
			OctValue ib = get(i, i^1).half().floor();
			for (int j = 0; j <= maxCol; ++j) {
				OctValue jb = get(j^1, j).half().floor();
				OctValue b = ib.add(jb);
				if (get(i, j).compareTo(b) > 0) {
					set(i, j, b);
				}
			}
		}		
	}

	/**
	 * Checks for negative self loops in the graph represented by this adjacency matrix.
	 * Self loops are represented by this matrix' diagonal elements.
	 * <p>
	 * <b>m</b> is strongly closed and has a negative self loop <=> <b>m</b> is empty in <b>R</b><br>
	 * <b>m</b> is tightly closed and has a negative self loop <=> <b>m</b> is empty in <b>Z</b>
	 * 
	 * @return a negative self loop exists
	 */
	public boolean hasNegativeSelfLoop() {
		for (int i = 0; i < mSize; ++i) {
			if (get(i, i).compareTo(OctValue.ZERO) < 0) {
				return true;
			}
		}
		return false;
	}

	@Override
	public String toString() {
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
}
