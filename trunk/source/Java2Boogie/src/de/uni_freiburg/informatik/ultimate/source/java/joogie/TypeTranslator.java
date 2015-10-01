package de.uni_freiburg.informatik.ultimate.source.java.joogie;

import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.types.BoogieArrayType;
import org.joogie.boogie.types.BoogieFieldType;
import org.joogie.boogie.types.BoogieObjectType;
import org.joogie.boogie.types.BoogiePrimitiveType;
import org.joogie.boogie.types.HeapType;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class TypeTranslator {

	public static ASTType translate(final org.joogie.boogie.types.BoogieType joogieType, final ILocation loc) {
		if (joogieType instanceof BoogieArrayType) {
			final BoogieArrayType arrType = (BoogieArrayType) joogieType;
			return new ArrayType(loc, new String[0], new ASTType[] { translate(arrType.getIndexType(), loc) },
					translate(arrType.getNestedType(), loc));
		} else if (joogieType instanceof BoogieFieldType) {
			return new NamedType(loc, joogieType.getName(),
					new ASTType[] { translate(((BoogieFieldType) joogieType).getNestedType(), loc) });
		} else if (joogieType instanceof BoogieObjectType) {
			return new NamedType(loc, joogieType.getName(), new ASTType[0]);
		} else if (joogieType instanceof BoogiePrimitiveType) {
			return new PrimitiveType(loc, translateJoogiePrimitiveStrings(joogieType.getName()));
		} else if (joogieType instanceof HeapType) {
			// Note: HeapType is a Joogie Hack! "<x>[ref, Field x]x"
			return new ArrayType(loc, new String[] { "x" },
					new ASTType[] { new NamedType(loc, "ref", new ASTType[0]),
							new NamedType(loc, "Field", new ASTType[] { new NamedType(loc, "x", new ASTType[0]) }) },
					new NamedType(loc, "x", new ASTType[0]));
		}

		throw new UnsupportedOperationException("Not yet implemented");

	}

	public static ASTType translate(Variable var, ILocation loc) {
		return translate(var.getType(), loc);
	}

	private static String translateJoogiePrimitiveStrings(final String primitiveString) {
		if (primitiveString.equals("int")) {
			return BoogieType.intType.toString();
		} else if (primitiveString.equals("realVar")) {
			return BoogieType.realType.toString();
		} else if (primitiveString == "bool") {
			return BoogieType.boolType.toString();
		} else if (primitiveString.startsWith("bv")) {
			int length = Integer.parseInt(primitiveString.substring(2));
			return BoogieType.createBitvectorType(length).toString();
		} else {
			// mLogger.fatal("getPrimitiveType called with unknown type " +
			// primitiveString + "!");
			throw new AssertionError("Type error. Cannot convert " + primitiveString);
		}
	}
}
