package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;

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
