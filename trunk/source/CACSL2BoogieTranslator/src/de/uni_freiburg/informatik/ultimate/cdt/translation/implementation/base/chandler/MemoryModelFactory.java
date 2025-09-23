package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.AbstractMap.SimpleEntry;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.CheckMode;

/**
 * The factory used to create concrete instances that are part of the {@link MemoryModel}.
 */
public class MemoryModelFactory {
	/**
	 * The factory method used to create an IMemoryPointer instance. Does all the checks if the given settings are
	 * valid.
	 *
	 * @return A concrete IMemoryPointer instance.
	 */
	public static IMemoryPointer createMemoryPointer(final TranslationSettings settings, final BoogieType boogieType,
			final TypeSizes typeSizes) {
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
					new SimpleEntry<>(CACSLPreferenceInitializer.LABEL_CHECK_MEMORY_NEUTRALITY,
							!settings.getFunctionsCheckedForMemoryNeutrality().isEmpty()),
					new SimpleEntry<>(CACSLPreferenceInitializer.LABEL_USE_CONSTANT_ARRAYS,
							settings.useConstantArrays()));

			final List<String> incompatibleActiveOptions =
					incompatibleOptions.stream().filter(SimpleEntry::getValue).map(SimpleEntry::getKey).toList();

			if (!incompatibleActiveOptions.isEmpty()) {
				throw new UnsupportedOperationException(memoryAddressingPreference
						+ " memory addressing is not compatible with the following active settings: "
						+ String.join(", ", incompatibleActiveOptions));
			}

			return MemoryPointer1D.create(settings, boogieType, typeSizes);
		case Two_Dimensional:
			return MemoryPointer2D.create(settings, boogieType, typeSizes);
		default:
			throw new UnsupportedOperationException(
					"MemoryAddressing: " + memoryAddressingPreference + " not implemented yet.");
		}
	}
}
