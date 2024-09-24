/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2024 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2024 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLType;

/**
 * Provides static methods for conversion from {@link ACSLType}s to C types.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class AcslTypeUtils {
	public static CType translateAcslTypeToCType(final ACSLType t) {
		// TODO: Handle non-primitive types as well
		return new CPrimitive(translatePrimitiveAcslTypeToCType(t));
	}

	private static CPrimitives translatePrimitiveAcslTypeToCType(final ACSLType t) {
		switch (t.getTypeName()) {
		case "char":
			return CPrimitives.CHAR;
		case "signed char":
			return CPrimitives.SCHAR;
		case "unsigned char":
			return CPrimitives.UCHAR;
		case "short":
		case "short int":
		case "signed short":
		case "signed short int":
			return CPrimitives.SHORT;
		case "unsigned short":
		case "unsigned short int":
			return CPrimitives.USHORT;
		case "int":
		case "signed int":
			return CPrimitives.INT;
		case "unsigned int":
		case "unsigned":
			return CPrimitives.UINT;
		case "long":
		case "long int":
		case "signed long":
		case "signed long int":
			return CPrimitives.LONG;
		case "unsigned long":
		case "unsigned long int":
			return CPrimitives.ULONG;
		case "long long":
		case "long long int":
		case "signed long long":
		case "signed long long int":
			return CPrimitives.LONGLONG;
		case "unsigned long long":
		case "unsigned long long int":
		case "size_t":
			return CPrimitives.ULONGLONG;
		case "__int128":
			return CPrimitives.INT128;
		case "unsigned __int128":
			return CPrimitives.UINT128;
		case "float":
			return CPrimitives.FLOAT;
		case "double":
			return CPrimitives.DOUBLE;
		case "long double":
			return CPrimitives.LONGDOUBLE;
		case "__float128":
			return CPrimitives.FLOAT128;
		case "_Bool":
			return CPrimitives.BOOL;
		default:
			throw new UnsupportedOperationException("Unhandled ACSL type " + t);
		}
	}

	public static ACSLType translateCTypeToAcslType(final CType type) {
		if (!(type instanceof CPrimitive)) {
			// TODO: Implement this for other types
			throw new UnsupportedOperationException(
					"Currently only primitive types are supported, got " + type.getClass().getSimpleName());
		}
		return new ACSLType(((CPrimitive) type).getType().getTypeName());
	}
}
