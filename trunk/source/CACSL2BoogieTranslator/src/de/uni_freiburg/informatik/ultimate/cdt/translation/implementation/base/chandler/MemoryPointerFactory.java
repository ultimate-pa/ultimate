package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;

/**
 * The factory used to create an IMemoryPointer instance.
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
