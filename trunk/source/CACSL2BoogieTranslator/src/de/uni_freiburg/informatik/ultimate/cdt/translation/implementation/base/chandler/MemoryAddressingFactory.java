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

/**
 * Factory class for creating instances of memory addressing schemes based on a specified {@link IMemoryPointer}
 * representation.
 *
 * This class provides a method to instantiate different memory addressing schemes dynamically depending on the
 * {@link IMemoryPointer} implementation.
 */
public class MemoryAddressingFactory {
	/**
	 * The factory method for creating the concrete memory structure instance.
	 *
	 * @return A concrete instance of IMemoryAdressing.
	 */
	public static IMemoryAdressing createMemoryAddressing(final TranslationSettings settings,
			final ITypeHandler typeHandler, final ExpressionTranslation exprTranslation,
			final IBooleanArrayHelper booleanArrayHelper, final TypeSizes typeSizes,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer, final FunctionDeclarations functionDeclarations,
			final IMemoryPointer pointer) {

		if (pointer instanceof final MemoryPointer1D p) {
			return new MemoryAddressing1D(typeHandler, exprTranslation, booleanArrayHelper, typeSizes,
					typeSizeAndOffsetComputer, settings, functionDeclarations, p);
		} else if (pointer instanceof final MemoryPointer2D p) {
			return new MemoryAddressing2D(typeHandler, exprTranslation, booleanArrayHelper, typeSizes,
					typeSizeAndOffsetComputer, settings.getPointerIntegerCastMode(), functionDeclarations, p);
		}

		throw new UnsupportedOperationException("Unknown pointer instance: " + pointer.getClass());
	}
}
