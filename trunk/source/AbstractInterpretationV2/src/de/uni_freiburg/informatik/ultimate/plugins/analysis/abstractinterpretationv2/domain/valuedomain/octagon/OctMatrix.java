package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.octagon;

import java.util.Arrays;
import java.util.function.BiFunction;

/**
 * Matrix for octagons (as presented by Antoine Mine).
 * <p>
 * 
 * TODO More documentation
 * TODO Stores entries for variables +v1, -v1, ..., +vn, -vn
 * TODO Variables (names, type, ...) aren't stored
 * TODO Matrix is divided into 2x2 blocks
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
	 * at least one element from the lower triangular matrix is completely
	 * stored. Elements are stored row-wise from top to bottom, left to right.
	 * 
	 * @see #indexOf(int, int)
	 */
	private final OctValue[] mElements;


	public OctMatrix(OctMatrix octMatrix) {
		mSize = octMatrix.mSize;
		mElements = new OctValue[octMatrix.mElements.length];
		System.arraycopy(octMatrix.mElements, 0, mElements, 0, mElements.length);
	}
	
	public OctMatrix(int variables) {
		mSize = variables * 2;
		mElements = new OctValue[2 * variables * (variables + 1)];
		Arrays.fill(mElements, OctValue.INFINITY);
		setMainDiagonal(OctValue.ZERO);
	}

	public int getSize() {
		return mSize;
	}
	
	public OctValue get(int row, int col) {
		return mElements[indexOf(row, col)];
	}
	
	protected void set(int row, int col, OctValue value) {
		if(value == null)
			throw new IllegalArgumentException("null is not a valid matrix element.");
		mElements[indexOf(row, col)] = value;
	}
	
	protected void setMainDiagonal(OctValue value) {
		for (int i = 0; i < mSize; ++i)
			mElements[indexOfLower(i, i)] = value;
	}

	private int indexOf(int row, int col) {
		if (row >= mSize || col >= mSize)
			throw new IndexOutOfBoundsException(row + "," + col + " is not an index for matrix of size " + mSize + ".");
		if (row < col)
			return indexOfLower(col ^ 1, row ^ 1);
		return indexOfLower(row, col);
	}

	private int indexOfLower(int row, int col) {
		return col + (row + 1) * (row + 1) / 2;
	}

	public OctMatrix elementwise(OctMatrix other, BiFunction<OctValue, OctValue, OctValue> operator) {
		if (other.mSize != mSize)
			throw new IllegalArgumentException("Incompatible matrices");
		OctMatrix result = new OctMatrix(mSize);
		for (int i = 0; i < mElements.length; ++i) // a loop is faster than a stream
			result.mElements[i] = operator.apply(mElements[i], other.mElements[i]);
		return result;
	}

	public OctMatrix add(OctMatrix other) {
		return elementwise(other, OctValue::add);
	}
	
	public OctMatrix min(OctMatrix other) {
		return elementwise(other, OctValue::min);
	}
	
	public OctMatrix max(OctMatrix other) {
		return elementwise(other, OctValue::max);
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
