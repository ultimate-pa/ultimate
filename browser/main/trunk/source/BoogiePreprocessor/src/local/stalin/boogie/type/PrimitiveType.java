package local.stalin.boogie.type;

import java.util.ArrayList;

public class PrimitiveType extends BoogieType {
	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -1842658349197318623L;
	public static final int BOOL  = -1;
	public static final int INT   = -2;
	public static final int REAL  = -3;
	public static final int ERROR = -42;
	
	/**
	 * The type code.  If this is >= 0, this is the length and the class
	 * represents a bit vector type of this length.  Otherwise, this is 
	 * one of BOOL, INT, REAL, or ERROR. 
	 */
	private final int type;
	
	PrimitiveType(int type) {
		this.type = type;
	}

	//@Override
	public BoogieType getUnderlyingType() {
		return this;
	}

	//@Override
	protected boolean hasPlaceholder(int minDepth, int maxDepth) {
		return false;
	}

	//@Override
	protected BoogieType incrementPlaceholders(int depth, int incDepth) {
		return this;
	}

	//@Override
	protected boolean isUnifiableTo(int depth, BoogieType other,
			ArrayList<BoogieType> subst) {
		if (other instanceof PlaceholderType)
			return other.isUnifiableTo(depth, this, subst);
		return this == errorType || other == errorType || this == other;
	}

	//@Override
	protected BoogieType substitutePlaceholders(int depth,
			BoogieType[] substType) {
		return this;
	}

	//@Override
	protected String toString(int depth, boolean needParentheses) {
		switch (type) {
		case INT:
			return "int";
		case BOOL:
			return "bool";
		case ERROR:
			return "*type-error*";
		default:
			return "bv"+type;
					
		}
	}

	//@Override
	protected boolean unify(int depth, BoogieType other,
			BoogieType[] substitution) {
		return this == errorType || other == errorType || this == other;
	}

	public int getTypeCode() {
		return type;
	}

	public boolean isFinite() {
		/* Everything except INT may be finite */
		return type != INT;
	}
}
