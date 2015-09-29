package de.uni_freiburg.informatik.ultimate.source.java;

import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.types.BoogieArrayType;
import org.joogie.boogie.types.BoogieFieldType;
import org.joogie.boogie.types.BoogieObjectType;
import org.joogie.boogie.types.BoogiePrimitiveType;
import org.joogie.boogie.types.BoogieType;
import org.joogie.boogie.types.HeapType;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class Joogie2BoogieUtil {

	public static ASTType getASTType(BoogieType joogieType) {
		if (joogieType instanceof BoogieArrayType) {

		} else if (joogieType instanceof BoogieFieldType) {

		} else if (joogieType instanceof BoogieObjectType) {

		} else if (joogieType instanceof BoogiePrimitiveType) {

		} else if (joogieType instanceof HeapType) {

		}

		throw new UnsupportedOperationException("Not yet implemented");

	}

	public static ASTType getASTType(Variable var) {
		return getASTType(var.getType());
	}
}
