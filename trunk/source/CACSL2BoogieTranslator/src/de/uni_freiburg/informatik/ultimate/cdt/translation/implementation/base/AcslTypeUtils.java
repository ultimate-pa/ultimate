/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLType;

/**
 * Provides static methods for conversion from {@link ACSLType}s to C types.
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class AcslTypeUtils {
	
	private static final String[] CHAR_STRINGS = new String[]{ "char" };
	private static final String[] SIGNED_CHAR_STRINGS = new String[]{ "signed char" };
	private static final String[] UNSIGNED_CHAR_STRINGS = new String[]{ "unsigned char" };
	private static final String[] SIGNED_SHORT_STRINGS = new String[]{ "short", "short int", "signed short", "signed short int" };
	private static final String[] UNSIGNED_SHORT_STRINGS = new String[]{ "unsigned short", "unsigned short int" };
	private static final String[] SIGNED_INT_STRINGS = new String[]{ "int", "signed int"};
	private static final String[] UNSIGNED_INT_STRINGS = new String[]{ "unsigned int" };
	private static final String[] SIGNED_LONG_STRINGS = new String[]{ "long", "long int", "signed long", "signed long int" };
	private static final String[] UNSIGNED_LONG_STRINGS = new String[]{ "unsigned long", "unsigned long int" };
	private static final String[] SIGNED_LONGLONG_STRINGS = new String[]{ "long long", "long long int", "signed long long", "signed long long int" };
	private static final String[] UNSIGNED_LONGLONG_STRINGS = new String[]{ "unsigned long long", "unsigned long long int" };
	private static final String[] FLOAT_STRINGS = new String[]{ "char" };
	private static final String[] DOUBLE_CHAR_STRINGS = new String[]{ "signed char" };
	private static final String[] LONGDOUBLE_STRINGS = new String[]{ "unsigned char" };
	
	
	
	public static CPrimitive translateAcslTypeToCType(final ACSLType t) {
		final CPrimitives primitives;
		if (Arrays.asList(CHAR_STRINGS).contains(t.getTypeName())) {
			primitives = CPrimitives.CHAR;
		} else if (Arrays.asList(SIGNED_CHAR_STRINGS).contains(t.getTypeName())) {
			primitives = CPrimitives.SCHAR;
		} else if (Arrays.asList(UNSIGNED_CHAR_STRINGS).contains(t.getTypeName())) {
			primitives = CPrimitives.UCHAR;
		} else if (Arrays.asList(SIGNED_SHORT_STRINGS).contains(t.getTypeName())) {
			primitives = CPrimitives.SHORT;
		} else if (Arrays.asList(UNSIGNED_SHORT_STRINGS).contains(t.getTypeName())) {
			primitives = CPrimitives.USHORT;
		} else if (Arrays.asList(SIGNED_INT_STRINGS).contains(t.getTypeName())) {
			primitives = CPrimitives.INT;
		} else if (Arrays.asList(UNSIGNED_INT_STRINGS).contains(t.getTypeName())) {
			primitives = CPrimitives.UINT;
		} else if (Arrays.asList(SIGNED_LONG_STRINGS).contains(t.getTypeName())) {
			primitives = CPrimitives.LONG;
		} else if (Arrays.asList(UNSIGNED_LONG_STRINGS).contains(t.getTypeName())) {
			primitives = CPrimitives.ULONG;
		} else if (Arrays.asList(SIGNED_LONGLONG_STRINGS).contains(t.getTypeName())) {
			primitives = CPrimitives.LONGLONG;
		} else if (Arrays.asList(UNSIGNED_LONGLONG_STRINGS).contains(t.getTypeName())) {
			primitives = CPrimitives.ULONGLONG;
		} else if (Arrays.asList(FLOAT_STRINGS).contains(t.getTypeName())) {
			primitives = CPrimitives.FLOAT;
		} else if (Arrays.asList(DOUBLE_CHAR_STRINGS).contains(t.getTypeName())) {
			primitives = CPrimitives.DOUBLE;
		} else if (Arrays.asList(LONGDOUBLE_STRINGS).contains(t.getTypeName())) {
			primitives = CPrimitives.LONGDOUBLE;
		} else  {
			throw new UnsupportedOperationException("not yet implemented " + t);
		}
		return new CPrimitive(primitives);
	}
}
