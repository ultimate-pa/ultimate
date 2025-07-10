package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.AbstractMap.SimpleEntry;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.CheckMode;

/**
 * The factory used to create concrete instances that are part of the {@link MemoryModel}.
 */
public class MemoryModelFactory {
	/**
	 * The factory method for creating the concrete memory structure instance.
	 *
	 * @param settings
	 *            The given settings.
	 * @return A concrete instance of IMemoryAdressing.
	 */
	public static IMemoryAdressing createMemoryAddressing(final TranslationSettings settings,
			final ITypeHandler typeHandler, final ExpressionTranslation exprTranslation,
			final IBooleanArrayHelper booleanArrayHelper, final TypeSizes typeSizes,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer) {
		final var memoryAddressingPreference = settings.memoryAddressingPreference();

		switch (memoryAddressingPreference) {
		case One_Dimensional:
			final List<SimpleEntry<String, Boolean>> incompatibleOptions = List.of(
					new SimpleEntry<>(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_DEREF_VALIDITY,
							settings.checkPointerDerefValidity() != CheckMode.IGNORE),
					new SimpleEntry<>(CACSLPreferenceInitializer.LABEL_CHECK_FREE_VALID,
							settings.checkIfFreedPointerIsValid()),
					new SimpleEntry<>(
							CACSLPreferenceInitializer.LABEL_CHECK_POINTER_SUBTRACTION_AND_COMPARISON_VALIDITY,
							settings.getPointerSubtractionAndComparisonValidityCheckMode() != CheckMode.IGNORE),
					new SimpleEntry<>(CACSLPreferenceInitializer.LABEL_BITVECTOR_TRANSLATION,
							settings.isBitvectorTranslation()));

			final List<String> incompatibleActiveOptions =
					incompatibleOptions.stream().filter(SimpleEntry::getValue).map(SimpleEntry::getKey).toList();

			if (!incompatibleActiveOptions.isEmpty()) {
				throw new UnsupportedOperationException(memoryAddressingPreference
						+ " memory addressing is not compatible with the following active settings: "
						+ String.join(", ", incompatibleActiveOptions));
			}
			return new OneDimensionalMemoryAddressing(typeHandler, exprTranslation, booleanArrayHelper, typeSizes,
					typeSizeAndOffsetComputer);
		case Two_Dimensional:
			return new TwoDimensionalMemoryAddressing(typeHandler, exprTranslation, booleanArrayHelper, typeSizes,
					typeSizeAndOffsetComputer);
		default:
			throw new UnsupportedOperationException(
					"MemoryAddressing: " + memoryAddressingPreference + " not implemented yet.");
		}
	}

	/**
	 * The factory method for creating the concrete memory structure instance.
	 *
	 * @param settings
	 *            The given settings.
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
			return new MemoryStructure_SingleBitprecise(memoryStructurePreference.getByteSize(), typeSizes,
					typeHandler);
		case HoenickeLindenmann_Original:
			if (settings.isBitvectorTranslation()) {
				return new MemoryStructure_MultiBitprecise(typeSizes, typeHandler);
			}
			return new MemoryStructure_Unbounded(typeSizes, typeHandler);
		default:
			throw new UnsupportedOperationException(memoryStructurePreference + " is an invalid memory structure.");

		}
	}
}
