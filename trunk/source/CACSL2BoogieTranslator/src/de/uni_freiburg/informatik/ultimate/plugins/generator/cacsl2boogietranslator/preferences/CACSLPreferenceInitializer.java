package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.TranslationMode;

public class CACSLPreferenceInitializer extends UltimatePreferenceInitializer {

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<TranslationMode>(LABEL_MODE,
						TranslationMode.BASE, PreferenceType.Radio,
						TranslationMode.values()),
				new UltimatePreferenceItem<String>(LABEL_MAINPROC, "",
						PreferenceType.String),
				new UltimatePreferenceItem<Boolean>(LABEL_CHECK_SVCOMP_ERRORFUNCTION,
						true, PreferenceType.Boolean),
				new UltimatePreferenceItem<POINTER_CHECKMODE>(
						LABEL_CHECK_POINTER_VALIDITY,
						POINTER_CHECKMODE.ASSERTandASSUME,
						PreferenceType.Combo, POINTER_CHECKMODE.values()),
				new UltimatePreferenceItem<POINTER_CHECKMODE>(
						LABEL_CHECK_POINTER_ALLOC,
						POINTER_CHECKMODE.ASSERTandASSUME,
						PreferenceType.Combo, POINTER_CHECKMODE.values()),
				new UltimatePreferenceItem<POINTER_CHECKMODE>(
						LABEL_CHECK_ARRAYACCESSOFFHEAP,
						POINTER_CHECKMODE.ASSERTandASSUME,
						PreferenceType.Combo, POINTER_CHECKMODE.values()),
				new UltimatePreferenceItem<Boolean>(LABEL_CHECK_FREE_VALID,
						true, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_CHECK_MemoryLeakInMain, false,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_CHECK_MallocNonNegative, false,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_REPORT_UNSOUNDNESS_WARNING, false,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<POINTER_CHECKMODE>(
						LABEL_CHECK_POINTER_SUBTRACTION_AND_COMPARISON_VALIDITY,
						POINTER_CHECKMODE.ASSERTandASSUME,
						PreferenceType.Combo, POINTER_CHECKMODE.values()),
				new UltimatePreferenceItem<UNSIGNED_TREATMENT>(
						LABEL_UNSIGNED_TREATMENT,
						UNSIGNED_TREATMENT.WRAPAROUND,
						PreferenceType.Combo, UNSIGNED_TREATMENT.values()),
				new UltimatePreferenceItem<Boolean>(
						LABEL_CHECK_SIGNED_INTEGER_BOUNDS,
						false,
						PreferenceType.Boolean),

				// typesize stuff
				new UltimatePreferenceItem<Boolean>(
						LABEL_USE_EXPLICIT_TYPESIZES, true,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_VOID, 1, PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_BOOL, 1, PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_CHAR, 1, PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_SHORT, 2,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_INT, 4, PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_LONG, 4, PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_FLOAT, 4,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_DOUBLE, 8,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						// LABEL_EXPLICIT_TYPESIZE_POINTER, 8,
						LABEL_EXPLICIT_TYPESIZE_POINTER, 4,
						PreferenceType.Integer),
				// more exotic types
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_SCHAR, 1,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_UCHAR, 1,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_WCHAR, 1,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_CHAR16, 2,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_CHAR32, 4,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_USHORT, 2,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_UINT, 4, PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_ULONG, 4,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_LONGLONG, 8,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_ULONGLONG, 8,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_COMPLEXFLOAT, 8,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_COMPLEXDOUBLE, 16,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_LONGDOUBLE, 12,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_COMPLEXLONGDOUBLE, 24,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_ENUM, 4, PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_EXPLICIT_TYPESIZE_DEFAULT, 4,
						PreferenceType.Integer) };
	}

	@Override
	protected String getPlugID() {
		return Activator.s_PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return "C+ACSL to Boogie Translator";
	}

	public enum POINTER_CHECKMODE {
		IGNORE, ASSUME, ASSERTandASSUME
	}

	public enum UNSIGNED_TREATMENT {
		IGNORE, ASSUME_SOME, ASSUME_ALL, WRAPAROUND
	}

	public static final String LABEL_MODE = "Translation Mode:";
	public static final String LABEL_MAINPROC = "Checked method. Library mode if empty.";
	public static final String LABEL_CHECK_SVCOMP_ERRORFUNCTION = "Check unreachability of error function in SV-COMP mode";
	public static final String LABEL_CHECK_POINTER_VALIDITY = "Pointer base address is valid at dereference";
	public static final String LABEL_CHECK_POINTER_ALLOC = "Pointer to allocated memory at dereference";
	public static final String LABEL_CHECK_FREE_VALID = "Check if freed pointer was valid";
	public static final String LABEL_CHECK_MemoryLeakInMain = "Check for the main procedure if all allocated memory was freed";
	public static final String LABEL_CHECK_MallocNonNegative = "Check if the input of malloc is non-negative";
	public static final String LABEL_CHECK_ARRAYACCESSOFFHEAP = "Check array bounds for arrays that are off heap";
	public static final String LABEL_REPORT_UNSOUNDNESS_WARNING = "Report unsoundness warnings";
	public static final String LABEL_CHECK_POINTER_SUBTRACTION_AND_COMPARISON_VALIDITY = "If two pointers are subtracted or compared they have the same base address";
	public static final String LABEL_UNSIGNED_TREATMENT = "How to treat unsigned ints differently from normal ones";
	public static final String LABEL_CHECK_SIGNED_INTEGER_BOUNDS = "Check that no signed integer over-/underflows occur";
						

	// typesize stuff
	public static final String LABEL_USE_EXPLICIT_TYPESIZES = "Use the constants given below as storage sizes for the correponding types";
	public static final String LABEL_EXPLICIT_TYPESIZE_VOID = "Size of void (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_BOOL = "Size of bool (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_CHAR = "Size of char (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_SHORT = "Size of short (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_INT = "Size of int (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_LONG = "Size of long (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_FLOAT = "Size of float (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_DOUBLE = "Size of double (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_POINTER = "Size of pointer (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_SCHAR = "Size of signed char (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_UCHAR = "Size of unsigned char (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_WCHAR = "Size of wchar (?) (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_CHAR16 = "Size of char16 (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_CHAR32 = "Size of char32 (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_USHORT = "Size of unsigned short (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_UINT = "Size of unsigned int (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_ULONG = "Size of unsigned long (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_LONGLONG = "Size of long long (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_ULONGLONG = "Size of unsigned long long (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_COMPLEXFLOAT = "Size of complex float (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_COMPLEXDOUBLE = "Size of complex double (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_LONGDOUBLE = "Size of long double (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_COMPLEXLONGDOUBLE = "Size of complex long double (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_ENUM = "Size of an enum (in bytes)";
	public static final String LABEL_EXPLICIT_TYPESIZE_DEFAULT = "Size of any base type not listed here (in bytes)";
}
