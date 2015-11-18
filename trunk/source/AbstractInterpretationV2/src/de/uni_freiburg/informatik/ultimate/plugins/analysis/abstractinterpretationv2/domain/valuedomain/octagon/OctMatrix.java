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
 * This class ensures that all elements on the main diagonal are 0
 * and each matrix is coherent (as seen in the following ASCII art).
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

	/** Size of this matrix (size = #rows = #columns). */
	private final int mSize;

	/** Offset of the strictly lower triangular matrix in {@link #mElements}. */
	private final int mOffsetLower;
	
	/**
	 * Stores the elements of this matrix.
	 * <p>
	 * Some elements are neglected because they are constant or coherent to
	 * other elements (see documentation of this class). The remaining
	 * elements are either part of "lower" (L) or "upper" (U) as seen in the
	 * following ASCII art.
	 * 
	 * <pre>
	 *     \ U - - - -            \ 0 - - - - 
	 *     L \ - - - -            3 \ - - - - 
	 *     L L \ U - -            4 5 \ 1 - - 
	 *     L L L \ - -            6 7 8 \ - - 
	 *     L L L L \ U            9 . . . \ 2 
	 *     L L L L L \            . . . . . \
	 *     stored parts             indexing
	 *    (only L and U)
	 *
	 * mElements: [ 0 1 2 3 4 5 6 7 8 9 ... ]
	 *              `-U-´ `-------L-------´
	 * </pre>
	 */
	private final OctValue[] mElements;


	public OctMatrix(OctMatrix octMatrix) {
		mSize = octMatrix.mSize;
		mOffsetLower = octMatrix.mOffsetLower;
		mElements = new OctValue[octMatrix.mElements.length];
		System.arraycopy(octMatrix.mElements, 0, mElements, 0, mElements.length);
	}
	
	public OctMatrix(int variables) {
		mSize = variables * 2;
		mOffsetLower = variables;
		mElements = new OctValue[mOffsetLower + mSize * (mSize - 1) / 2];
		Arrays.fill(mElements, OctValue.INFINITY);
	}

	public int getSize() {
		return mSize;
	}
	
	public OctValue get(int row, int col) {
		if (row == col)
			return OctValue.ZERO;
		return mElements[indexOf(row, col)];
	}
	
	protected void set(int row, int col, OctValue value) {
		if(value == null)
			throw new IllegalArgumentException("null is not a valid matrix element.");
		mElements[indexOf(row, col)] = value;
	}

	private int indexOf(int row, int col) {
		if (row >= mSize || col >= mSize)
			throw new IndexOutOfBoundsException(row + "," + col + " is not an index for matrix of size " + mSize + ".");
		if (row > col)
			return indexOfLower(row, col);
		if (row == col)
			return -1;
		if ((row ^ col) == 1) // && row < col
			return col / 2;
		return indexOfLower(col ^ 1, row ^ 1);
	}

	private int indexOfLower(int row, int col) {
		//                      triangle above row   +  offset in row
		return mOffsetLower  +  (row - 1) * row / 2  +  col;
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
