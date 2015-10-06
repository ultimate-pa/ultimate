/**
 * 
 */
package org.joogie.boogie.types;

/**
 * @author schaef
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class BoogiePreludeTypes {
	public static final BoogiePrimitiveType TYPE_INT = new BoogiePrimitiveType("int");
	public static final BoogiePrimitiveType TYPE_BOOL = new BoogiePrimitiveType("bool");
	public static final BoogiePrimitiveType TYPE_REAL = new BoogiePrimitiveType("realVar");
	public static final BoogieObjectType TYPE_CLASS_CONST = new BoogieObjectType("classConst");
	public static final BoogieObjectType TYPE_REF = new BoogieObjectType("ref");
	public static final BoogieObjectType TYPE_VOID = new BoogieObjectType("void");

	public static final BoogieArrayType TYPE_INT_ARRAY = new IntArrayType("intArray");
	public static final BoogieArrayType TYPE_REAL_ARRAY = new RealArrayType("realArray");
	public static final BoogieArrayType TYPE_REF_ARRAY = new RefArrayType("refArray", TYPE_REF);

	public static final BoogieFieldType TYPE_FIELD = new BoogieFieldType("Field", new BoogieObjectType("x"));

//	public static final String NAME_FIELD = "Field";
}
