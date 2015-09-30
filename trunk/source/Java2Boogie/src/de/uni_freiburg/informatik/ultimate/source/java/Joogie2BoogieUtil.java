package de.uni_freiburg.informatik.ultimate.source.java;

import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.types.BoogieArrayType;
import org.joogie.boogie.types.BoogieFieldType;
import org.joogie.boogie.types.BoogieObjectType;
import org.joogie.boogie.types.BoogiePrimitiveType;
import org.joogie.boogie.types.BoogieType;
import org.joogie.boogie.types.HeapType;

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
public final class Joogie2BoogieUtil {

	public static ASTType getASTType(final BoogieType joogieType, final ILocation loc) {
		if (joogieType instanceof BoogieArrayType) {
			BoogieArrayType arrType = (BoogieArrayType) joogieType;
			return new ArrayType(loc, null, new ASTType[] { getASTType(arrType.getIndexType(), loc) },
					getASTType(arrType.getNestedType(), loc));
		} else if (joogieType instanceof BoogieFieldType) {
			return new NamedType(loc, joogieType.getName(),
					new ASTType[] { getASTType(((BoogieFieldType) joogieType).getNestedType(), loc) });
		} else if (joogieType instanceof BoogieObjectType) {
			// Note: The BoogieObjectType implementation translates hardcoded to
			// "ref"
			return new NamedType(loc, joogieType.getName(), null);
		} else if (joogieType instanceof BoogiePrimitiveType) {
			return new PrimitiveType(loc, joogieType.getName());
		} else if (joogieType instanceof HeapType) {
			// Note: HeapType is a Joogie Hack! "<x>[ref, Field x]x"
			return new ArrayType(loc, new String[] { "x" },
					new ASTType[] { new NamedType(loc, "ref", null),
							new NamedType(loc, "Field", new ASTType[] { new NamedType(loc, "x", null) }) },
					new NamedType(loc, "x", null));
		}

		throw new UnsupportedOperationException("Not yet implemented");

	}

	public static ASTType getASTType(Variable var, ILocation loc) {
		return getASTType(var.getType(), loc);
	}
}
