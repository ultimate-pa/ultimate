package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.AbstractMap.SimpleEntry;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
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
	 * This enum represents the valid combinations of memory structure and memory adressing.
	 */
	private enum Combinations {
		ONE_Dimensional_SingleBitPrecise(OneDimensionalMemoryAddressing.class, MemoryStructure_SingleBitprecise.class),
		ONE_Dimensional_MultiBitPrecise(OneDimensionalMemoryAddressing.class, MemoryStructure_MultiBitprecise.class),
		ONE_Dimensional_Unbounded(OneDimensionalMemoryAddressing.class, MemoryStructure_Unbounded.class),
		TWO_Dimensional_MultiBitPrecise(TwoDimensionalMemoryAddressing.class, MemoryStructure_MultiBitprecise.class),
		TWO_Dimensional_SingleBitPrecise(TwoDimensionalMemoryAddressing.class, MemoryStructure_SingleBitprecise.class),
		TWO_Dimensional_Unbounded(TwoDimensionalMemoryAddressing.class, MemoryStructure_Unbounded.class);

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
	public static MemoryModel create(final TranslationSettings settings, final ITypeHandler typeHandler,
			final ExpressionTranslation exprTranslation, final IBooleanArrayHelper booleanArrayHelper,
			final TypeSizes typeSizes, final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer,
			final FunctionDeclarations functionDeclarations, final IMemoryPointer pointer) {
		final var addressing = createAddressing(settings, typeHandler, exprTranslation, booleanArrayHelper, typeSizes,
				typeSizeAndOffsetComputer, functionDeclarations, pointer);
		final var structure = createStructure(settings, typeSizes, typeHandler);

		if (!Combinations.isValid(addressing.getClass(), structure.getClass())) {
			throw new UnsupportedOperationException("The combination of addressing: " + addressing.getClass()
					+ " and structure " + structure.getClass() + " is invalid!");
		}

		return new MemoryModel(addressing, structure);
	}

	/**
	 * The factory method for creating the concrete memory structure instance.
	 *
	 * @return A concrete instance of IMemoryAdressing.
	 */
	private static IMemoryAdressing createAddressing(final TranslationSettings settings, final ITypeHandler typeHandler,
			final ExpressionTranslation exprTranslation, final IBooleanArrayHelper booleanArrayHelper,
			final TypeSizes typeSizes, final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer,
			final FunctionDeclarations functionDeclarations, final IMemoryPointer pointer) {

		if (pointer instanceof final OneDimensionalPointer p) {
			return new OneDimensionalMemoryAddressing(typeHandler, exprTranslation, booleanArrayHelper, typeSizes,
					typeSizeAndOffsetComputer, settings.getPointerIntegerCastMode(), functionDeclarations, p);
		} else if (pointer instanceof final TwoDimensionalPointer p) {
			return new TwoDimensionalMemoryAddressing(typeHandler, exprTranslation, booleanArrayHelper, typeSizes,
					typeSizeAndOffsetComputer, settings.getPointerIntegerCastMode(), functionDeclarations, p);
		}

		throw new UnsupportedOperationException("Unknown pointer instance: " + pointer.getClass());
	}

	/**
	 * The factory method for creating the concrete memory structure instance.
	 *
	 * @return A concrete instance of IMemoryStructure.
	 */
	private static IMemoryStructure createStructure(final TranslationSettings settings, final TypeSizes typeSizes,
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

			return new OneDimensionalPointer(boogieType, typeSizes);
		case Two_Dimensional:
			return new TwoDimensionalPointer(boogieType, typeSizes);
		default:
			throw new UnsupportedOperationException(
					"MemoryAddressing: " + memoryAddressingPreference + " not implemented yet.");
		}
	}
}
