/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.BitvectorTranslation.SmtRoundingMode;
import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.TranslationMode;

/**
 * Defines preference page for C translation.
 *
 * Check https://wiki.debian.org/ArchitectureSpecificsMemo to find our which setting for typesizes you want to use.
 *
 * @author Matthias Heizmann
 *
 */
public class CACSLPreferenceInitializer extends UltimatePreferenceInitializer {

	private static final String MAINPROC_DESC =
			"Specify the entry function of the program. " + "Use an empty string for library mode "
					+ "(i.e., assume all globals are non-deterministic and verify each function in isolation).";
	public static final String LABEL_MODE = "Translation Mode:";
	public static final String MAINPROC_LABEL = "Entry function";
	private static final String MAINPROC_DEFAULT = "main";
	public static final String LABEL_CHECK_SVCOMP_ERRORFUNCTION =
			"Check unreachability of error function in SV-COMP mode";
	public static final String LABEL_CHECK_POINTER_VALIDITY = "Pointer base address is valid at dereference";
	public static final String LABEL_CHECK_POINTER_ALLOC = "Pointer to allocated memory at dereference";
	public static final String LABEL_CHECK_FREE_VALID = "Check if freed pointer was valid";
	public static final String LABEL_CHECK_MEMORY_LEAK_IN_MAIN =
			"Check for the main procedure if all allocated memory was freed";
	public static final String LABEL_SVCOMP_MEMTRACK_COMPATIBILITY_MODE = "SV-COMP memtrack compatibility mode";
	public static final String DESC_SVCOMP_MEMTRACK_COMPATIBILITY_MODE = "Report UNKNOWN instead of UNSAFE if not all "
			+ "allocated memory was freed at the end of the main procedure. Rationale: at the SV-COMP we have to check "
			+ "if the program lost track of allocated memory. If this is set to false we are unsound (at SV-COMP) in "
			+ "cases where not all memory is freed but pointers to that memory are live at the end of the "
			+ "main procedure.";
	public static final String LABEL_MEMORY_MODEL = "Memory model";
	public static final String LABEL_POINTER_INTEGER_CONVERSION = "Pointer-integer casts";
	public static final String LABEL_CHECK_ARRAYACCESSOFFHEAP = "Check array bounds for arrays that are off heap";
	public static final String LABEL_REPORT_UNSOUNDNESS_WARNING = "Report unsoundness warnings";
	public static final String LABEL_BITPRECISE_BITFIELDS = "Bitprecise bitfields";
	public static final String LABEL_CHECK_POINTER_SUBTRACTION_AND_COMPARISON_VALIDITY =
			"If two pointers are subtracted or compared they have the same base address";
	public static final String LABEL_UNSIGNED_TREATMENT = "How to treat unsigned ints differently from normal ones";
	public static final String LABEL_CHECK_DIVISION_BY_ZERO_OF_INTEGER_TYPES = "Check division by zero";
	public static final String LABEL_CHECK_DIVISION_BY_ZERO_OF_FLOATING_TYPES =
			"Check division by zero for floating types";
	public static final String LABEL_CHECK_SIGNED_INTEGER_BOUNDS = "Check absence of signed integer overflows";
	public static final String LABEL_ASSUME_NONDET_VALUES_IN_RANGE = "Assume nondeterminstic values are in range";
	public static final String LABEL_BITVECTOR_TRANSLATION = "Use bitvectors instead of ints";
	public static final String LABEL_OVERAPPROXIMATE_FLOATS = "Overapproximate operations on floating types";
	private static final String DESC_OVERAPPROXIMATE_FLOATS =
			"Overapproximate all operations on floats (including plus, minus, multiplication, conversions, etc.) by "
					+ "havoc. The resulting analysis will be fast and sound, but the result is UNKNOWN if such an "
					+ "operation occurs in a counterexample.";
	public static final String LABEL_FP_TO_IEEE_BV_EXTENSION = "Use Z3's non-standard fp.to_ieee_bv extension";

	public static final String LABEL_FP_ROUNDING_MODE_INITIAL = "Initial rounding mode";
	private static final String DESC_FP_ROUNDING_MODE_INITIAL =
			"Use the specified rounding mode as initial float rounding mode.";
	private static final FloatingPointRoundingMode DEF_FP_ROUNDING_MODE_INITIAL =
			FloatingPointRoundingMode.FE_TONEAREST;

	public static final String LABEL_FP_ROUNDING_MODE_ENABLE_FESETROUND = "Let fesetround change the rounding mode";
	private static final boolean DEF_FP_ROUNDING_MODE_ENABLE_FESETROUND = true;
	private static final String DESC_FP_ROUNDING_MODE_ENABLE_FESETROUND =
			"If enabled, fesetround can change the current rounding mode. If disabled, fesetround does nothing and "
					+ "always returns non-zero (no success).";

	public static final String LABEL_SMT_BOOL_ARRAYS_WORKAROUND = "SMT bool arrays workaround";

	// typesize stuff
	public static final String LABEL_USE_EXPLICIT_TYPESIZES =
			"Use the constants given below as storage sizes for the correponding types";
	public static final String LABEL_EXPLICIT_TYPESIZE_BOOL = "sizeof _Bool";
	public static final String LABEL_EXPLICIT_TYPESIZE_CHAR = "sizeof char";
	public static final String LABEL_EXPLICIT_TYPESIZE_SHORT = "sizeof short";
	public static final String LABEL_EXPLICIT_TYPESIZE_INT = "sizeof int";
	public static final String LABEL_EXPLICIT_TYPESIZE_LONG = "sizeof long";
	public static final String LABEL_EXPLICIT_TYPESIZE_LONGLONG = "sizeof long long";
	public static final String LABEL_EXPLICIT_TYPESIZE_FLOAT = "sizeof float";
	public static final String LABEL_EXPLICIT_TYPESIZE_DOUBLE = "sizeof double";
	public static final String LABEL_EXPLICIT_TYPESIZE_LONGDOUBLE = "sizeof long double";
	public static final String LABEL_EXPLICIT_TYPESIZE_POINTER = "sizeof POINTER";
	// public static final String LABEL_EXPLICIT_TYPESIZE_CHAR16 = "sizeof char16";
	// public static final String LABEL_EXPLICIT_TYPESIZE_CHAR32 = "sizeof char32";
	public static final String LABEL_SIGNEDNESS_CHAR = "signedness of char";
	public static final String LABEL_CHECK_ALLOCATION_PURITY = "Check allocation purity";
	public static final String LABEL_USE_CONSTANT_ARRAYS = "Use constant arrays";
	private static final String DESC_USE_CONSTANT_ARRAYS =
			"Use SMT constant arrays for default initialization of variables.";
	public static final String LABEL_USE_STORE_CHAINS = "Use store chains";

	public static final String LABEL_ADAPT_MEMORY_MODEL_ON_POINTER_CASTS =
			"Adapt memory model on pointer casts if necessary";
	public static final String DESC_ADAPT_MEMORY_MODEL_ON_POINTER_CASTS = "When a pointer to a value with a small type "
			+ "(e.g. char) is cast to a larger pointer type (e.g. int*), and the memory model resolution is larger than "
			+ "the values's pointed to type size (for char: 1 Byte), the memory model is unsound. When this setting is "
			+ "on we attempt to detect this case, and automatically set the memory model to a higher resolution.";

	public enum PointerCheckMode {
		IGNORE, ASSUME, ASSERTandASSUME
	}

	public enum UnsignedTreatment {
		IGNORE, ASSERT, WRAPAROUND
	}

	public enum Signedness {
		SIGNED, UNSIGNED
	}

	public enum MemoryModel {
		HoenickeLindenmann_Original, // one data array for each boogie type

		HoenickeLindenmann_1ByteResolution,

		HoenickeLindenmann_2ByteResolution,

		HoenickeLindenmann_4ByteResolution,

		HoenickeLindenmann_8ByteResolution;

		public int getByteSize() {
			switch (this) {
			case HoenickeLindenmann_1ByteResolution:
				return 1;
			case HoenickeLindenmann_2ByteResolution:
				return 2;
			case HoenickeLindenmann_4ByteResolution:
				return 4;
			case HoenickeLindenmann_8ByteResolution:
				return 8;
			case HoenickeLindenmann_Original:
				throw new AssertionError("HoenickeLindenmann_Original has no associated byte size");
			default:
				throw new AssertionError("missing case/MemoryModel?");
			}
		}

		public boolean isBitVectorMemoryModel() {
			switch (this) {
			case HoenickeLindenmann_1ByteResolution:
			case HoenickeLindenmann_2ByteResolution:
			case HoenickeLindenmann_4ByteResolution:
			case HoenickeLindenmann_8ByteResolution:
				return true;
			case HoenickeLindenmann_Original:
				return false;
			default:
				throw new AssertionError("missing case/MemoryModel?");
			}
		}

		public static MemoryModel getPreciseEnoughMemoryModelFor(final int byteSize) {
			if (byteSize >= 8) {
				return HoenickeLindenmann_8ByteResolution;
			} else if (byteSize >= 4) {
				return HoenickeLindenmann_4ByteResolution;
			} else if (byteSize >= 2) {
				return HoenickeLindenmann_2ByteResolution;
			} else if (byteSize >= 1) {
				return HoenickeLindenmann_1ByteResolution;
			} else {
				throw new IllegalArgumentException("byte size smaller than 1 makes no sense");
			}
		}
	}

	public enum PointerIntegerConversion {
		Overapproximate, NonBijectiveMapping, NutzBijection, IdentityAxiom,
	}

	public enum FloatingPointRoundingMode {
		/**
		 * rounding towards negative infinity
		 */
		FE_DOWNWARD(SmtRoundingMode.RTN),
		/**
		 * rounding towards nearest integer
		 *
		 * TODO: Is RNE really the correct SMT rounding mode?
		 */
		FE_TONEAREST(SmtRoundingMode.RNE),
		/**
		 * rounding towards zero
		 */
		FE_TOWARDZERO(SmtRoundingMode.RTZ),
		/**
		 * rounding towards positive infinity
		 */
		FE_UPWARD(SmtRoundingMode.RTP);

		private final SmtRoundingMode mSmtRoundingMode;

		private FloatingPointRoundingMode(final SmtRoundingMode smtRoundingMode) {
			mSmtRoundingMode = smtRoundingMode;
		}

		public SmtRoundingMode getSmtRoundingMode() {
			return mSmtRoundingMode;
		}

	}

	public CACSLPreferenceInitializer() {
		super(Activator.PLUGIN_ID, "C+ACSL to Boogie Translator");
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {

		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<>(LABEL_MODE, TranslationMode.SV_COMP14, PreferenceType.Radio,
						TranslationMode.values()),
				new UltimatePreferenceItem<>(MAINPROC_LABEL, MAINPROC_DEFAULT, MAINPROC_DESC, PreferenceType.String),
				new UltimatePreferenceItem<>(LABEL_CHECK_SVCOMP_ERRORFUNCTION, true, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_CHECK_POINTER_VALIDITY, PointerCheckMode.ASSERTandASSUME,
						PreferenceType.Combo, PointerCheckMode.values()),
				new UltimatePreferenceItem<>(LABEL_CHECK_POINTER_ALLOC, PointerCheckMode.ASSERTandASSUME,
						PreferenceType.Combo, PointerCheckMode.values()),
				new UltimatePreferenceItem<>(LABEL_CHECK_ARRAYACCESSOFFHEAP, PointerCheckMode.ASSERTandASSUME,
						PreferenceType.Combo, PointerCheckMode.values()),
				new UltimatePreferenceItem<>(LABEL_CHECK_FREE_VALID, true, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_CHECK_MEMORY_LEAK_IN_MAIN, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_SVCOMP_MEMTRACK_COMPATIBILITY_MODE, false,
						DESC_SVCOMP_MEMTRACK_COMPATIBILITY_MODE, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_CHECK_ALLOCATION_PURITY, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_MEMORY_MODEL, MemoryModel.HoenickeLindenmann_Original,
						PreferenceType.Combo, MemoryModel.values()),
				new UltimatePreferenceItem<>(LABEL_POINTER_INTEGER_CONVERSION,
						PointerIntegerConversion.NonBijectiveMapping, PreferenceType.Combo,
						PointerIntegerConversion.values()),
				new UltimatePreferenceItem<>(LABEL_REPORT_UNSOUNDNESS_WARNING, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_BITPRECISE_BITFIELDS, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_CHECK_POINTER_SUBTRACTION_AND_COMPARISON_VALIDITY,
						PointerCheckMode.ASSERTandASSUME, PreferenceType.Combo, PointerCheckMode.values()),
				new UltimatePreferenceItem<>(LABEL_UNSIGNED_TREATMENT, UnsignedTreatment.WRAPAROUND,
						PreferenceType.Combo, UnsignedTreatment.values()),
				new UltimatePreferenceItem<>(LABEL_CHECK_DIVISION_BY_ZERO_OF_INTEGER_TYPES,
						PointerCheckMode.ASSERTandASSUME, PreferenceType.Combo, PointerCheckMode.values()),
				new UltimatePreferenceItem<>(LABEL_CHECK_DIVISION_BY_ZERO_OF_FLOATING_TYPES, PointerCheckMode.IGNORE,
						PreferenceType.Combo, PointerCheckMode.values()),
				new UltimatePreferenceItem<>(LABEL_CHECK_SIGNED_INTEGER_BOUNDS, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_ASSUME_NONDET_VALUES_IN_RANGE, true, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_BITVECTOR_TRANSLATION, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_OVERAPPROXIMATE_FLOATS, false, DESC_OVERAPPROXIMATE_FLOATS,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_FP_TO_IEEE_BV_EXTENSION, false, PreferenceType.Boolean),

				new UltimatePreferenceItem<>(LABEL_FP_ROUNDING_MODE_ENABLE_FESETROUND,
						DEF_FP_ROUNDING_MODE_ENABLE_FESETROUND, DESC_FP_ROUNDING_MODE_ENABLE_FESETROUND,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_FP_ROUNDING_MODE_INITIAL, DEF_FP_ROUNDING_MODE_INITIAL,
						DESC_FP_ROUNDING_MODE_INITIAL, PreferenceType.Combo, FloatingPointRoundingMode.values()),

				new UltimatePreferenceItem<>(LABEL_SMT_BOOL_ARRAYS_WORKAROUND, true, PreferenceType.Boolean),

				// typesize stuff
				new UltimatePreferenceItem<>(LABEL_USE_EXPLICIT_TYPESIZES, true, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_EXPLICIT_TYPESIZE_BOOL, 1, PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_EXPLICIT_TYPESIZE_CHAR, 1, PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_EXPLICIT_TYPESIZE_SHORT, 2, PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_EXPLICIT_TYPESIZE_INT, 4, PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_EXPLICIT_TYPESIZE_LONG, 8, PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_EXPLICIT_TYPESIZE_LONGLONG, 8, PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_EXPLICIT_TYPESIZE_FLOAT, 4, PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_EXPLICIT_TYPESIZE_DOUBLE, 8, PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_EXPLICIT_TYPESIZE_LONGDOUBLE, 16, PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_EXPLICIT_TYPESIZE_POINTER, 8, PreferenceType.Integer),
				// more exotic types
				// new UltimatePreferenceItem<Integer>(
				// LABEL_EXPLICIT_TYPESIZE_CHAR16, 2, PreferenceType.Integer),
				// new UltimatePreferenceItem<Integer>(
				// LABEL_EXPLICIT_TYPESIZE_CHAR32, 4, PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_SIGNEDNESS_CHAR, Signedness.SIGNED, PreferenceType.Combo,
						Signedness.values()),
				new UltimatePreferenceItem<>(LABEL_USE_CONSTANT_ARRAYS, false, DESC_USE_CONSTANT_ARRAYS,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_USE_STORE_CHAINS, false, "Only for benchmarking -- do not use",
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_ADAPT_MEMORY_MODEL_ON_POINTER_CASTS, false,
						DESC_ADAPT_MEMORY_MODEL_ON_POINTER_CASTS, PreferenceType.Boolean) };

	}
}
