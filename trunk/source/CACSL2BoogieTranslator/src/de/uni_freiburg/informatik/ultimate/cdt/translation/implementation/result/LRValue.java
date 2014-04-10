package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;

public abstract class LRValue {
	
	/**
	 * Abstract class constructor -- all inheritors of LRValue have at least
	 * an expression representing what the containing result evaluates to.
	 * @param value
	 */
	public LRValue () {
	}
	
	public abstract Expression getValue();
	
	public CType cType;
	
	/** 
	 * This flag is supposed to be true iff the value-expression of this
	 * LRValue is of boolean type in boogie.  
	 * For instance if it is the translation of an comparator expression
	 * like x == 0.
	 */
	public boolean isBoogieBool;
	
//	public boolean isPointer;
	
//	public boolean isOnHeap;
	
	public String toString() {
		if (this instanceof HeapLValue)
			return "address: " + ((HeapLValue) this).getAddress();
		else if (this instanceof LocalLValue)
			return "lhs: " + ((LocalLValue) this).getLHS();
		else
			return "value: " + this.getValue();
	}

}
