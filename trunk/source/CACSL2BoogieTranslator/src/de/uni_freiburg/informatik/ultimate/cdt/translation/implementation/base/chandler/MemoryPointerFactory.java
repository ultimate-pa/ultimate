/*
 * Copyright (C) 2025 Jan Körner
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

package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;

/**
 * Factory class for creating an instance of a memory pointer representation.
 *
 * This class provides a method to instantiate various memory pointer representations depending on the selected
 * translation settings.
 *
 * @author Jan Körner
 */
public abstract class MemoryPointerFactory {
	/**
	 * The factory method used to create an IMemoryPointer instance.
	 *
	 * @return A IMemoryPointer instance.
	 */
	public static IMemoryPointer createMemoryPointer(final TranslationSettings settings, final BoogieType boogieType,
			final TypeSizes typeSizes) {
		final var memoryAddressingPreference = settings.memoryAddressingPreference();

		switch (memoryAddressingPreference) {
		case One_Dimensional:
			return MemoryPointer1D.create(settings, boogieType, typeSizes);
		case Two_Dimensional:
			return MemoryPointer2D.create(settings, boogieType, typeSizes);
		default:
			throw new UnsupportedOperationException(
					"MemoryAddressing: " + memoryAddressingPreference + " not implemented yet.");
		}
	}
}
