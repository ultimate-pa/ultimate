package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util;

import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctagonDomainState;

/**
 * Utility functions for type-handling, especially in {@link OctagonDomainState}.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class TypeUtil {

	public static boolean isBoolean(IType type) {
		if (type instanceof PrimitiveType) {
			int typeCode = ((PrimitiveType) type).getTypeCode();
			return typeCode == PrimitiveType.BOOL;
		}
		return false;
	}

	public static boolean isNumeric(IType type) {
		if (type instanceof PrimitiveType) {
			int typeCode = ((PrimitiveType) type).getTypeCode();
			return  typeCode == PrimitiveType.INT || typeCode == PrimitiveType.REAL;
		}
		return false;
	}

	public static boolean isNumericNonInt(IType type) {
		if (type instanceof PrimitiveType) {
			int typeCode = ((PrimitiveType) type).getTypeCode();
			return typeCode == PrimitiveType.REAL;
		}
		return false;
	}
	
	public static boolean isNumericInt(IType type) {
		if (type instanceof PrimitiveType) {
			int typeCode = ((PrimitiveType) type).getTypeCode();
			return typeCode == PrimitiveType.INT;
		}
		return false;
	}

	/**
	 * Checks if two Boogie types are of the same type category.
	 * There are three type categories:
	 * <ul>
	 * 		<li>numeric (int, real)</li>
	 * 		<li>boolean (bool)</li>
	 * 		<li>unsupported (bit-vectors, arrays, ...)</li>
	 * </ul>
	 *
	 * @param a first type
	 * @param b second type
	 * @return a and b are of the same type category
	 */
	public static boolean categoryEquals(IType a, IType b) {
		return (isBoolean(a) == isBoolean(b)) && (isNumeric(a) == isNumeric(b));
	}

}
