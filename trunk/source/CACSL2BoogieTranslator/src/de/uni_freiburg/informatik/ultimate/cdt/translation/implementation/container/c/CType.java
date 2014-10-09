/**
 * Abstract class to describe a variable declaration given in C.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;


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
}
