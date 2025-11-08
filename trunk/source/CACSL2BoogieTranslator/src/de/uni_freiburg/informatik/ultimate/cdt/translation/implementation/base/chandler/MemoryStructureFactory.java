package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;

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

		switch (memoryStructurePreference) {
		case HoenickeLindenmann_1ByteResolution:
		case HoenickeLindenmann_2ByteResolution:
		case HoenickeLindenmann_4ByteResolution:
		case HoenickeLindenmann_8ByteResolution:
			return new MemoryStructureSingleBitprecise(memoryStructurePreference.getByteSize(), typeSizes, typeHandler);
		case HoenickeLindenmann_Original:
			if (settings.isBitvectorTranslation()) {
				return new MemoryStructureMultiBitprecise(typeSizes, typeHandler);
			}
			return new MemoryStructureUnbounded(typeSizes, typeHandler);
		default:
			throw new UnsupportedOperationException(memoryStructurePreference + " is an invalid memory structure.");
		}
	}
}
