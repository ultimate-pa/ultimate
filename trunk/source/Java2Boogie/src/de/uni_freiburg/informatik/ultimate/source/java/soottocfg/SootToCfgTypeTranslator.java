package de.uni_freiburg.informatik.ultimate.source.java.soottocfg;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import soottocfg.cfg.Variable;
import soottocfg.cfg.type.BoolType;
import soottocfg.cfg.type.IntType;
import soottocfg.cfg.type.Type;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class SootToCfgTypeTranslator {

	public static ASTType translate(final Type type, final ILocation loc) {
		if (type instanceof BoolType) {
			return new PrimitiveType(loc, BoogieType.boolType.toString());
		} else if (type instanceof IntType) {
			return new PrimitiveType(loc, BoogieType.intType.toString());
		}

		throw new UnsupportedOperationException(
				"Type not yet implemented: " + (type == null ? "null" : type.getClass().getSimpleName()));

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
