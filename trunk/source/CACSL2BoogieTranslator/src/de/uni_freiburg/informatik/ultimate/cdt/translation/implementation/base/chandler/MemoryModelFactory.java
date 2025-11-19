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

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;

public class MemoryModelFactory {
	/**
	 * This enum represents the valid combinations of memory structure and memory adressing.
	 */
	private enum Combinations {
		ONE_Dimensional_SingleBitPrecise(MemoryAddressing1D.class, MemoryStructureSingleBitprecise.class),
		ONE_Dimensional_MultiBitPrecise(MemoryAddressing1D.class, MemoryStructureMultiBitprecise.class),
		ONE_Dimensional_Unbounded(MemoryAddressing1D.class, MemoryStructureUnbounded.class),
		TWO_Dimensional_MultiBitPrecise(MemoryAddressing2D.class, MemoryStructureMultiBitprecise.class),
		TWO_Dimensional_SingleBitPrecise(MemoryAddressing2D.class, MemoryStructureSingleBitprecise.class),
		TWO_Dimensional_Unbounded(MemoryAddressing2D.class, MemoryStructureUnbounded.class);

		private final Class<? extends IMemoryAdressing> mAddressingType;
		private final Class<? extends IMemoryStructure> mStructureType;

		Combinations(final Class<? extends IMemoryAdressing> addressingType,
				final Class<? extends IMemoryStructure> structureType) {
			mAddressingType = addressingType;
			mStructureType = structureType;
		}

		/**
		 * Checks if the given combination is a valid one.
		 *
		 * @return If it is valid.
		 */
		public static boolean isValid(final Class<? extends IMemoryAdressing> addressingType,
				final Class<? extends IMemoryStructure> structureType) {
			for (final var value : values()) {
				if (value.mAddressingType.equals(addressingType) && value.mStructureType.equals(structureType)) {
					return true;
				}
			}
			return false;
		}
	}

	/**
	 * The factory method that creates a memory model with a valid combination of addressing and structure.
	 *
	 * @return The memory model.
	 */
	public static MemoryModel createMemoryModel(final TranslationSettings settings, final ITypeHandler typeHandler,
			final ExpressionTranslation exprTranslation, final IBooleanArrayHelper booleanArrayHelper,
			final TypeSizes typeSizes, final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer,
			final FunctionDeclarations functionDeclarations, final IMemoryPointer pointer) {
		final var addressing = MemoryAddressingFactory.createMemoryAddressing(settings, typeHandler, exprTranslation,
				booleanArrayHelper, typeSizes, typeSizeAndOffsetComputer, functionDeclarations, pointer);
		final var structure = MemoryStructureFactory.createMemoryStructure(settings, typeSizes, typeHandler);

		if (!Combinations.isValid(addressing.getClass(), structure.getClass())) {
			throw new UnsupportedOperationException("The combination of addressing: " + addressing.getClass()
					+ " and structure " + structure.getClass() + " is invalid!");
		}

		return new MemoryModel(addressing, structure);
	}
}
