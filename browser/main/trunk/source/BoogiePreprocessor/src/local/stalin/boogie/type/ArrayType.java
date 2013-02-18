package local.stalin.boogie.type;
import java.util.ArrayList;

public class ArrayType extends BoogieType {
	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -8089266195576415316L;
	private final int numPlaceholders;
	private final BoogieType[] indexTypes;
	private final BoogieType valueType;
	private final BoogieType realType;
	private final boolean isFinite;
		
	ArrayType(int numPlaceholders, BoogieType[] indexTypes,
			BoogieType valueType) {
		this.numPlaceholders = numPlaceholders;
		this.indexTypes = indexTypes;
		this.valueType = valueType;
		
		boolean changed = false;
		BoogieType   realValueType = valueType.getUnderlyingType();
		if (realValueType != valueType)
			changed = true;
		BoogieType[] realIndexTypes = new BoogieType[indexTypes.length];
		for (int i = 0; i < realIndexTypes.length; i++) {
			realIndexTypes[i] = indexTypes[i].getUnderlyingType();
			if (realIndexTypes[i] != indexTypes[i])
				changed = true;
		}
		if (changed)
			realType = createArrayType(numPlaceholders, realIndexTypes, realValueType);
		else
			realType = this;
		boolean finite = realValueType.isFinite();
		for (BoogieType indexType : realIndexTypes)
			finite &= indexType.isFinite();
		this.isFinite = finite;
	}


	//@Override
	protected BoogieType substitutePlaceholders(int depth, BoogieType[] substType) {
		depth += numPlaceholders;
		boolean changed = false;
		BoogieType newValueType = valueType.substitutePlaceholders(depth, substType);
		if (newValueType != valueType)
			changed = true;
		BoogieType[] newIndexTypes = new BoogieType[indexTypes.length];
		for (int i = 0; i < indexTypes.length; i++) {
			newIndexTypes[i] = indexTypes[i].substitutePlaceholders(depth, substType);
			if (newIndexTypes[i] != indexTypes[i])
				changed = true;
		}
		if (changed)
			return createArrayType(numPlaceholders, newIndexTypes, newValueType);
		return this;
	}

	//@Override
	protected BoogieType incrementPlaceholders(int depth, int incDepth) {
		depth += numPlaceholders;
		boolean changed = false;
		BoogieType newValueType = valueType.incrementPlaceholders(depth, incDepth);
		if (newValueType != valueType)
			changed = true;
		BoogieType[] newIndexTypes = new BoogieType[indexTypes.length];
		for (int i = 0; i < indexTypes.length; i++) {
			newIndexTypes[i] = indexTypes[i].incrementPlaceholders(depth, incDepth);
			if (newIndexTypes[i] != indexTypes[i])
				changed = true;
		}
		if (changed)
			return createArrayType(numPlaceholders, newIndexTypes, newValueType);
		return this;
	}

	//@Override
	public BoogieType getUnderlyingType() {
		return realType;
	}
	

	/**
	 * Get the number of placeholder (type variables) used in this array type.
	 * @return the number of placeholder.
	 */
	public int getNumPlaceholders() {
		return numPlaceholders;
	}

	/**
	 * Get the number of indices, i.e. the dimension of the array.
	 * @return the number of indices.
	 */
	public int getIndexCount() {
		return indexTypes.length;
	}

	/**
	 * Returns the index type, i.e. the type of the index
	 * arguments at the given dimension. 
	 * @param dim the dimension. We must have 0 <= dim < getIndexCount().
	 * @return the index type.
	 */
	public BoogieType getIndexType(int dim) {
		return indexTypes[dim];
	}

	/**
	 * Returns the value type of the array, i.e. the type of the elements stored 
	 * in the arrray. 
	 * @return the value type.
	 */
	public BoogieType getValueType() {
		return valueType;
	}


	//@Override
	protected boolean unify(int depth, BoogieType other, BoogieType[] substitution) {
		if (other == errorType)
			return true;
		if (!(other instanceof ArrayType))
			return false;
		ArrayType type = (ArrayType) other;
		if (type.numPlaceholders != numPlaceholders
			|| type.indexTypes.length != indexTypes.length)
			return false;
		depth += numPlaceholders;
		for (int i = 0; i < indexTypes.length; i++) {
			if (!indexTypes[i].unify(depth, type.indexTypes[i], substitution))
				return false;
		}
		return valueType.unify(depth, type.valueType, substitution);
	}
	
	protected boolean hasPlaceholder(int minDepth, int maxDepth) {
		minDepth += numPlaceholders;
		maxDepth += numPlaceholders;
		for (BoogieType t : indexTypes) {
			if (t.hasPlaceholder(minDepth, maxDepth))
				return true;
		}
		return valueType.hasPlaceholder(minDepth, maxDepth); 
	}

	//@Override
	protected boolean isUnifiableTo(int depth, BoogieType other, ArrayList<BoogieType> subst) {
		if (this == other || other == errorType)
			return true;
		if (other instanceof PlaceholderType)
			return other.isUnifiableTo(depth, this, subst);
		if (!(other instanceof ArrayType))
			return false;
		ArrayType type = (ArrayType) other;
		if (type.numPlaceholders != numPlaceholders
			|| type.indexTypes.length != indexTypes.length)
			return false;
		depth += numPlaceholders;
		for (int i = 0; i < indexTypes.length; i++) {
			if (!indexTypes[i].isUnifiableTo(depth, type.indexTypes[i], subst))
				return false;
		}
		return valueType.isUnifiableTo(depth, type.valueType, subst);
	}
	
	/**
	 * Computes a string representation.  It uses depth to compute artificial
	 * names for the placeholders.
	 * @param depth the number of placeholders outside this expression.
	 * @param needParentheses true if parentheses should be set for constructed types
	 * @return a string representation of this array type.
	 */
	protected String toString(int depth, boolean needParentheses) {
		StringBuilder sb = new StringBuilder();
		String delim;
		if (needParentheses)
			sb.append("(");
		if (numPlaceholders > 0) {
			sb.append("<");
			delim ="";
			for (int i = 0; i < numPlaceholders; i++) {
				sb.append(delim).append("$"+(depth+i));
				delim = ",";
			}
			sb.append(">");
		}
		sb.append("[");
		delim = "";
		for (BoogieType iType : indexTypes) {
			sb.append(delim).append(iType.toString(depth+numPlaceholders, false));
			delim = ",";
		}
		sb.append("]");
		sb.append(valueType.toString(depth+numPlaceholders, false));
		if (needParentheses)
			sb.append(")");
		return sb.toString();
	}
	
	//@Override
	public boolean isFinite() {
		return isFinite;
	}
}
