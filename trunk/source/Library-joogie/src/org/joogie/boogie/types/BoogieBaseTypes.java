/**
 * 
 */
package org.joogie.boogie.types;

/**
 * @author schaef
 *
 */
public class BoogieBaseTypes {
	private static BoogiePrimitiveType intType = new BoogiePrimitiveType("int");
	private static BoogiePrimitiveType boolType = new BoogiePrimitiveType(
			"bool");
	private static BoogiePrimitiveType realType = new BoogiePrimitiveType(
			"realVar");
	private static BoogiePrimitiveType classConstType = new BoogiePrimitiveType(
			"classConst");
	private static BoogieObjectType refType = new BoogieObjectType("ref");
	private static BoogieObjectType voidType = new BoogieObjectType("void");

	private static BoogieArrayType intArrType = new IntArrayType("intArray");
	private static BoogieArrayType realArrType = new RealArrayType("realArray");
	private static BoogieArrayType refArrType = new RefArrayType("refArray",
			refType);


	public static BoogiePrimitiveType getClassConstType() {
		return classConstType;
	}

	public static BoogiePrimitiveType getIntType() {
		return intType;
	}

	public static BoogiePrimitiveType getRealType() {
		return realType;
	}

	public static BoogiePrimitiveType getBoolType() {
		return boolType;
	}
	
	public static BoogieObjectType getRefType() {
		return refType;
	}

	public static BoogieArrayType getIntArrType() {
		return intArrType;
	}

	public static BoogieArrayType getRealArrType() {
		return realArrType;
	}

	public static BoogieArrayType getRefArrType() {
		return refArrType;
	}

	public static BoogieObjectType getVoidType() {
		return voidType;
	}
	
}
