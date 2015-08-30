/**
 * Abstract class to describe a variable declaration given in C.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.GENERALPRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;


/**
 * @author Markus Lindenmann
 * @date 18.09.2012
 * @author nutz
 */
public abstract class CType {

	/* C type modifiers */
	protected boolean isConst, isInline, isRestrict, isVolatile;

	public boolean isConst() {
		return isConst;
	}

	public boolean isInline() {
		return isInline;
	}

	public boolean isRestrict() {
		return isRestrict;
	}

	public boolean isVolatile() {
		return isVolatile;
	}
	
	public boolean isIncomplete() {
		return false;
	}

	/**
	 * Constructor.
	 */
	public CType(boolean isConst, boolean isInline, boolean isRestrict, boolean isVolatile) {
		this.isConst = isConst;
		this.isInline = isInline;
		this.isRestrict = isRestrict;
		this.isVolatile = isVolatile;
	}

	@Override
	public abstract String toString();

	/**
	 * @param cType
	 *            CType object
	 * @return the underlying type in case of CNamed, else the input object
	 */
	public CType getUnderlyingType() {
		if (this instanceof CNamed) {
			return ((CNamed) this).getUnderlyingType();
		}
		return this;
	}

	/**
	 * This is a special notion of type compatibility that we use for matching function signatures.
	 * -- i.e. for the most part we say void is "compatible" with everything..
	 * TODO: think about how general this notion is..
	 * @param cT
	 * @return
	 */
	public abstract boolean isCompatibleWith(CType cT);

	/*
	 * All subtypes shall implement equals and hashCode..
	 * .. but we can't ensure it via abstract methods because we need Object.equals sometimes
	 */
//	public boolean equals(Object o);
//	public abstract int hashCode();
	
	
	/**
	 * Returns true iff this type is an integer type according to the
	 * definition 6.2.5.7 in the C11 standard.
	 */
	public boolean isIntegerType() {
		if (this instanceof CPrimitive) {
			return (((CPrimitive) this).getGeneralType() == GENERALPRIMITIVE.INTTYPE);
		} else if (this instanceof CEnum) {
			return true;
		} else {
			return false;
		}
	}
	
	/**
	 * Returns true iff this type is a real floating type according to the
	 * definition 6.2.5.10 of the C11 standard.
	 */
	public boolean isRealFloatingType() {
		if (this instanceof CPrimitive) {
			CPrimitive cPrimitive = (CPrimitive) this;
			return cPrimitive.getType() == PRIMITIVE.FLOAT || 
					cPrimitive.getType() == PRIMITIVE.DOUBLE || 
					cPrimitive.getType() == PRIMITIVE.LONGDOUBLE;
		} else {
			return false;
		}
	}
	
	/**
	 * Returns true iff this type is a complex type according to the
	 * definition 6.2.5.11 of the C11 standard.
	 */
	public boolean isComplexType() {
		if (this instanceof CPrimitive) {
			CPrimitive cPrimitive = (CPrimitive) this;
			return cPrimitive.getType() == PRIMITIVE.COMPLEX_FLOAT|| 
					cPrimitive.getType() == PRIMITIVE.COMPLEX_DOUBLE || 
					cPrimitive.getType() == PRIMITIVE.COMPLEX_LONGDOUBLE;
		} else {
			return false;
		}
	}
	
	/**
	 * Returns true iff this type is an floating type according to the
	 * definition 6.2.5.11 in the C11 standard.
	 */
	public boolean isFloatingType() {
		if (this instanceof CPrimitive) {
			return (((CPrimitive) this).getGeneralType() == GENERALPRIMITIVE.FLOATTYPE);
		} else {
			return false;
		}
	}
	
	/**
	 * Returns true iff this type is a real type according to the
	 * definition 6.2.5.17 in the C11 standard.
	 */
	public boolean isRealType() {
		return this.isIntegerType() || this.isRealFloatingType();
	}
	
	/**
	 * Returns true iff this type is an arithmetic type according to the
	 * definition 6.2.5.18 in the C11 standard.
	 */
	public boolean isArithmeticType() {
		return this.isIntegerType() || this.isFloatingType();
	}
	
	/**
	 * Returns true iff this type is a scalar type according to the
	 * definition 6.2.5.21 in the C11 standard.
	 */
	public boolean isScalarType() {
		return (this instanceof CPointer) || isArithmeticType();
	}
		
}
