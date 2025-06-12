/*
 * Copyright (C) 2025 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2025 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library;

import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;

/**
 * Model of stdint.h (C11 7.20, https://en.cppreference.com/w/c/header/stdint) that defines additional integer types.
 */
public class StdintLibraryModel implements ILibraryModel {

	@Override
	public Collection<TypeModel> getTypeModels() {
		// TODO: These types depend on the settings, but they should have always the specified bits
		final var int8 = new CPrimitive(CPrimitives.SCHAR);
		final var int16 = new CPrimitive(CPrimitives.SHORT);
		final var int32 = new CPrimitive(CPrimitives.INT);
		final var int64 = new CPrimitive(CPrimitives.LONGLONG);

		final var uint8 = new CPrimitive(CPrimitives.UCHAR);
		final var uint16 = new CPrimitive(CPrimitives.USHORT);
		final var uint32 = new CPrimitive(CPrimitives.UINT);
		final var uint64 = new CPrimitive(CPrimitives.ULONGLONG);

		return List.of(
				// signed integer type with width of exactly 8, 16, 32 and 64 bits respectively
				new TypeModel("int8_t", int8), new TypeModel("int16_t", int16), new TypeModel("int32_t", int32),
				new TypeModel("int64_t", int64),

				// fastest signed integer type with width of at least 8, 16, 32 and 64 bits respectively
				new TypeModel("int_fast8_t", int8), new TypeModel("int_fast16_t", int16),
				new TypeModel("int_fast32_t", int32), new TypeModel("int_fast64_t", int64),

				// smallest signed integer type with width of at least 8, 16, 32 and 64 bits respectively
				new TypeModel("int_least8_t", int8), new TypeModel("int_least16_t", int16),
				new TypeModel("int_least32_t", int32), new TypeModel("int_least64_t", int64),

				// maximum width integer type
				new TypeModel("intmax_t", int64),

				// integer type capable of holding a pointer
				new TypeModel("intptr_t", int32),

				// unsigned integer type with width of exactly 8, 16, 32 and 64 bits respectively
				new TypeModel("uint8_t", uint8), new TypeModel("uint16_t", uint16), new TypeModel("uint32_t", uint32),
				new TypeModel("uint64_t", uint64),

				// fastest unsigned integer type with width of at least 8, 16, 32 and 64 bits respectively
				new TypeModel("uint_fast8_t", uint8), new TypeModel("uint_fast16_t", uint16),
				new TypeModel("uint_fast32_t", uint32), new TypeModel("uint_fast64_t", uint64),

				// smallest unsigned integer type with width of at least 8, 16, 32 and 64 bits respectively
				new TypeModel("uint_least8_t", uint8), new TypeModel("uint_least16_t", uint16),
				new TypeModel("uint_least32_t", uint32), new TypeModel("uint_least64_t", uint64),

				// maximum width unsigned integer type
				new TypeModel("uintmax_t", uint64),

				// unsigned integer type capable of holding a pointer
				new TypeModel("uintptr_t", uint32));
	}

	@Override
	public Collection<ConstantModel> getConstantModels() {
		// TODO: Add INTN_MIN etc.
		return List.of();
	}

}
