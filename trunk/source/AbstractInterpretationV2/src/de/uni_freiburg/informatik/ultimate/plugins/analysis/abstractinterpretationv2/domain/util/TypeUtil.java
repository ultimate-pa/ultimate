package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util;

import de.uni_freiburg.informatik.ultimate.boogie.type.ConstructedType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctDomainState;

/**
 * Utility functions for type-handling, especially in {@link OctDomainState}.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class TypeUtil {

	private final static Integer INT = PrimitiveType.INT;
	private final static Integer REAL = PrimitiveType.REAL;
	private final static Integer BOOL = PrimitiveType.BOOL;

	public static boolean isBoolean(IBoogieType type) {
		return BOOL.equals(primitiveType(type));
	}

	public static boolean isNumeric(IBoogieType type) {
		final Integer t = primitiveType(type);
		return INT.equals(t) || REAL.equals(t);
	}

	public static boolean isNumericNonInt(IBoogieType type) {
		return REAL.equals(primitiveType(type));
	}

	public static boolean isNumericInt(IBoogieType type) {
		return INT.equals(primitiveType(type));
	}

	private static Integer primitiveType(IBoogieType type) {
		if (type instanceof PrimitiveType) {
			return ((PrimitiveType) type).getTypeCode();
		} else if (type instanceof ConstructedType) {
			final ConstructedType ctype = (ConstructedType) type;
			if (ctype.getUnderlyingType() instanceof ConstructedType) {
				return null;
			}
			return primitiveType(ctype.getUnderlyingType());
		}
		return null;
	}

	/**
	 * Checks if two Boogie types are of the same type category. There are three type categories:
	 * <ul>
	 * <li>numeric (int, real)</li>
	 * <li>boolean (bool)</li>
	 * <li>unsupported (bit-vectors, arrays, ...)</li>
	 * </ul>
	 *
	 * @param a
	 *            first type
	 * @param b
	 *            second type
	 * @return a and b are of the same type category
	 */
	public static boolean categoryEquals(IBoogieType a, IBoogieType b) {
		return (isBoolean(a) == isBoolean(b)) && (isNumeric(a) == isNumeric(b));
	}

	public static boolean isIntTerm(Term t) {
		return "Int".equals(t.getSort().getRealSort().getName());
	}

	public static boolean isRealTerm(Term t) {
		return "Real".equals(t.getSort().getRealSort().getName());
	}

}
