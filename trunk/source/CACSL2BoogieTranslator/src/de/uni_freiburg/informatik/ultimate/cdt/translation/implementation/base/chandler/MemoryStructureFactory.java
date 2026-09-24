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

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;

/**
 * Factory class for creating an instance of a memory structure.
 *
 * This class provides a method to instantiate various memory structure implementations depending on the selected
 * translation settings.
 *
 * @author Jan Körner
 */
public class MemoryStructureFactory {
	/**
	 * The factory method for creating the concrete memory structure instance.
	 *
	 * @return A concrete instance of IMemoryStructure.
	 */
	public static IMemoryStructure createMemoryStructure(final TranslationSettings settings, final TypeSizes typeSizes,
			final ITypeHandler typeHandler) {
		final var memoryStructurePreference = settings.getMemoryStructurePreference();
		if (memoryStructurePreference.isBitVectorRepresentation() && !settings.isBitvectorTranslation()) {
			throw new UnsupportedOperationException("Memory Structure: " + memoryStructurePreference
					+ " is only available in using the bitprecise translation");
		}

		return switch (memoryStructurePreference) {
		case HoenickeLindenmann_1ByteResolution:
		case HoenickeLindenmann_2ByteResolution:
		case HoenickeLindenmann_4ByteResolution:
		case HoenickeLindenmann_8ByteResolution:
			yield new MemoryStructureSingleBitprecise(memoryStructurePreference.getByteSize(), typeSizes, typeHandler);
		case HoenickeLindenmann_Original:
			if (settings.isBitvectorTranslation()) {
				yield new MemoryStructureMultiBitprecise(typeSizes, typeHandler);
			}
			yield new MemoryStructureUnbounded(typeSizes, typeHandler);
		};
	}
}
