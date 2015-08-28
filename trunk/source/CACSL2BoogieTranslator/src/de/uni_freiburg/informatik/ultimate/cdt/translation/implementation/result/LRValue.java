package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;

/**
 * 
 * @author Alexander Nutz, Matthias Heizmann
 *
 */
public abstract class LRValue {
	
	/**
	 * Abstract class constructor -- all inheritors of LRValue have at least
	 * an expression representing what the containing result evaluates to.
	 * @param value
	 */
	public LRValue () {
	}
	
	private CType cType;
	
	/** 
	 * This flag is supposed to be true iff the value-expression of this
	 * LRValue is of boolean type in boogie.  
	 * For instance if it is the translation of a comparator expression
	 * like x == 0.
	 */
	private boolean isBoogieBool;

	private boolean isIntFromPointer;

	
	public abstract Expression getValue();
	
	public CType getCType() {
		return cType;
	}

	public void setCType(CType cType) {
		this.cType = cType;
	}

	public boolean isBoogieBool() {
		return isBoogieBool;
	}

	public void setBoogieBool(boolean isBoogieBool) {
		this.isBoogieBool = isBoogieBool;
	}

	public boolean isIntFromPointer() {
		return isIntFromPointer;
	}

	public void setIntFromPointer(boolean isIntFromPointer) {
		this.isIntFromPointer = isIntFromPointer;
	}
	
	public final String toString() {
		if (this instanceof HeapLValue)
			return "address: " + ((HeapLValue) this).getAddress();
		else if (this instanceof LocalLValue)
			return "lhs: " + ((LocalLValue) this).getLHS();
		else
			return "value: " + this.getValue();
	}

}
