/*
 * Copyright (C) 2022 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE CDTParser plug-in.
 *
 * The ULTIMATE CDTParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CDTParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CDTParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CDTParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CDTParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.parser;

import java.util.Arrays;
import java.util.List;

import org.eclipse.cdt.core.language.settings.providers.ILanguageSettingsProvider;
import org.eclipse.cdt.core.language.settings.providers.LanguageSettingsStorage;
import org.eclipse.cdt.core.settings.model.CMacroEntry;
import org.eclipse.cdt.core.settings.model.ICConfigurationDescription;
import org.eclipse.cdt.core.settings.model.ICLanguageSettingEntry;
import org.eclipse.cdt.core.settings.model.ICSettingEntry;
import org.eclipse.core.resources.IResource;

/**
 * A {@link ILanguageSettingsProvider} that provides the builtin results detected by
 * org.eclipse.cdt.managedbuilder.core.GCCBuiltinSpecsDetector from a GCC 8.3.0.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class GccStaticLanguageSettingsProvider implements ILanguageSettingsProvider {

	private final List<ICLanguageSettingEntry> mSettings;

	public GccStaticLanguageSettingsProvider() {
		final ICLanguageSettingEntry[] entries = { createEntry("WIN64", "1"), createEntry("WINNT", "1"),
				createEntry("_INTEGRAL_MAX_BITS", "64"), createEntry("_REENTRANT", "1"), createEntry("_WIN32", "1"),
				createEntry("_WIN64", "1"), createEntry("__ATOMIC_ACQUIRE", "2"), createEntry("__ATOMIC_ACQ_REL", "4"),
				createEntry("__ATOMIC_CONSUME", "1"), createEntry("__ATOMIC_HLE_ACQUIRE", "65536"),
				createEntry("__ATOMIC_HLE_RELEASE", "131072"), createEntry("__ATOMIC_RELAXED", "0"),
				createEntry("__ATOMIC_RELEASE", "3"), createEntry("__ATOMIC_SEQ_CST", "5"),
				createEntry("__BIGGEST_ALIGNMENT__", "16"), createEntry("__BYTE_ORDER__", "__ORDER_LITTLE_ENDIAN__"),
				createEntry("__CHAR16_TYPE__", "short unsigned int"), createEntry("__CHAR32_TYPE__", "unsigned int"),
				createEntry("__CHAR_BIT__", "8"), createEntry("__DBL_DECIMAL_DIG__", "17"),
				createEntry("__DBL_DENORM_MIN__", "((double)4.94065645841246544176568792868221372e-324L)"),
				createEntry("__DBL_DIG__", "15"),
				createEntry("__DBL_EPSILON__", "((double)2.22044604925031308084726333618164062e-16L)"),
				createEntry("__DBL_HAS_DENORM__", "1"), createEntry("__DBL_HAS_INFINITY__", "1"),
				createEntry("__DBL_HAS_QUIET_NAN__", "1"), createEntry("__DBL_MANT_DIG__", "53"),
				createEntry("__DBL_MAX_10_EXP__", "308"), createEntry("__DBL_MAX_EXP__", "1024"),
				createEntry("__DBL_MAX__", "((double)1.79769313486231570814527423731704357e+308L)"),
				createEntry("__DBL_MIN_10_EXP__", "(-307)"), createEntry("__DBL_MIN_EXP__", "(-1021)"),
				createEntry("__DBL_MIN__", "((double)2.22507385850720138309023271733240406e-308L)"),
				createEntry("__DEC128_EPSILON__", "1E-33DL"), createEntry("__DEC128_MANT_DIG__", "34"),
				createEntry("__DEC128_MAX_EXP__", "6145"),
				createEntry("__DEC128_MAX__", "9.999999999999999999999999999999999E6144DL"),
				createEntry("__DEC128_MIN_EXP__", "(-6142)"), createEntry("__DEC128_MIN__", "1E-6143DL"),
				createEntry("__DEC128_SUBNORMAL_MIN__", "0.000000000000000000000000000000001E-6143DL"),
				createEntry("__DEC32_EPSILON__", "1E-6DF"), createEntry("__DEC32_MANT_DIG__", "7"),
				createEntry("__DEC32_MAX_EXP__", "97"), createEntry("__DEC32_MAX__", "9.999999E96DF"),
				createEntry("__DEC32_MIN_EXP__", "(-94)"), createEntry("__DEC32_MIN__", "1E-95DF"),
				createEntry("__DEC32_SUBNORMAL_MIN__", "0.000001E-95DF"), createEntry("__DEC64_EPSILON__", "1E-15DD"),
				createEntry("__DEC64_MANT_DIG__", "16"), createEntry("__DEC64_MAX_EXP__", "385"),
				createEntry("__DEC64_MAX__", "9.999999999999999E384DD"), createEntry("__DEC64_MIN_EXP__", "(-382)"),
				createEntry("__DEC64_MIN__", "1E-383DD"),
				createEntry("__DEC64_SUBNORMAL_MIN__", "0.000000000000001E-383DD"),
				createEntry("__DECIMAL_BID_FORMAT__", "1"), createEntry("__DECIMAL_DIG__", "21"),
				createEntry("__DEC_EVAL_METHOD__", "2"), createEntry("__FINITE_MATH_ONLY__", "0"),
				createEntry("__FLOAT_WORD_ORDER__", "__ORDER_LITTLE_ENDIAN__"),
				createEntry("__FLT128_DECIMAL_DIG__", "36"),
				createEntry("__FLT128_DENORM_MIN__", "6.47517511943802511092443895822764655e-4966F128"),
				createEntry("__FLT128_DIG__", "33"),
				createEntry("__FLT128_EPSILON__", "1.92592994438723585305597794258492732e-34F128"),
				createEntry("__FLT128_HAS_DENORM__", "1"), createEntry("__FLT128_HAS_INFINITY__", "1"),
				createEntry("__FLT128_HAS_QUIET_NAN__", "1"), createEntry("__FLT128_MANT_DIG__", "113"),
				createEntry("__FLT128_MAX_10_EXP__", "4932"), createEntry("__FLT128_MAX_EXP__", "16384"),
				createEntry("__FLT128_MAX__", "1.18973149535723176508575932662800702e+4932F128"),
				createEntry("__FLT128_MIN_10_EXP__", "(-4931)"), createEntry("__FLT128_MIN_EXP__", "(-16381)"),
				createEntry("__FLT128_MIN__", "3.36210314311209350626267781732175260e-4932F128"),
				createEntry("__FLT32X_DECIMAL_DIG__", "17"),
				createEntry("__FLT32X_DENORM_MIN__", "4.94065645841246544176568792868221372e-324F32x"),
				createEntry("__FLT32X_DIG__", "15"),
				createEntry("__FLT32X_EPSILON__", "2.22044604925031308084726333618164062e-16F32x"),
				createEntry("__FLT32X_HAS_DENORM__", "1"), createEntry("__FLT32X_HAS_INFINITY__", "1"),
				createEntry("__FLT32X_HAS_QUIET_NAN__", "1"), createEntry("__FLT32X_MANT_DIG__", "53"),
				createEntry("__FLT32X_MAX_10_EXP__", "308"), createEntry("__FLT32X_MAX_EXP__", "1024"),
				createEntry("__FLT32X_MAX__", "1.79769313486231570814527423731704357e+308F32x"),
				createEntry("__FLT32X_MIN_10_EXP__", "(-307)"), createEntry("__FLT32X_MIN_EXP__", "(-1021)"),
				createEntry("__FLT32X_MIN__", "2.22507385850720138309023271733240406e-308F32x"),
				createEntry("__FLT32_DECIMAL_DIG__", "9"),
				createEntry("__FLT32_DENORM_MIN__", "1.40129846432481707092372958328991613e-45F32"),
				createEntry("__FLT32_DIG__", "6"),
				createEntry("__FLT32_EPSILON__", "1.19209289550781250000000000000000000e-7F32"),
				createEntry("__FLT32_HAS_DENORM__", "1"), createEntry("__FLT32_HAS_INFINITY__", "1"),
				createEntry("__FLT32_HAS_QUIET_NAN__", "1"), createEntry("__FLT32_MANT_DIG__", "24"),
				createEntry("__FLT32_MAX_10_EXP__", "38"), createEntry("__FLT32_MAX_EXP__", "128"),
				createEntry("__FLT32_MAX__", "3.40282346638528859811704183484516925e+38F32"),
				createEntry("__FLT32_MIN_10_EXP__", "(-37)"), createEntry("__FLT32_MIN_EXP__", "(-125)"),
				createEntry("__FLT32_MIN__", "1.17549435082228750796873653722224568e-38F32"),
				createEntry("__FLT64X_DECIMAL_DIG__", "21"),
				createEntry("__FLT64X_DENORM_MIN__", "3.64519953188247460252840593361941982e-4951F64x"),
				createEntry("__FLT64X_DIG__", "18"),
				createEntry("__FLT64X_EPSILON__", "1.08420217248550443400745280086994171e-19F64x"),
				createEntry("__FLT64X_HAS_DENORM__", "1"), createEntry("__FLT64X_HAS_INFINITY__", "1"),
				createEntry("__FLT64X_HAS_QUIET_NAN__", "1"), createEntry("__FLT64X_MANT_DIG__", "64"),
				createEntry("__FLT64X_MAX_10_EXP__", "4932"), createEntry("__FLT64X_MAX_EXP__", "16384"),
				createEntry("__FLT64X_MAX__", "1.18973149535723176502126385303097021e+4932F64x"),
				createEntry("__FLT64X_MIN_10_EXP__", "(-4931)"), createEntry("__FLT64X_MIN_EXP__", "(-16381)"),
				createEntry("__FLT64X_MIN__", "3.36210314311209350626267781732175260e-4932F64x"),
				createEntry("__FLT64_DECIMAL_DIG__", "17"),
				createEntry("__FLT64_DENORM_MIN__", "4.94065645841246544176568792868221372e-324F64"),
				createEntry("__FLT64_DIG__", "15"),
				createEntry("__FLT64_EPSILON__", "2.22044604925031308084726333618164062e-16F64"),
				createEntry("__FLT64_HAS_DENORM__", "1"), createEntry("__FLT64_HAS_INFINITY__", "1"),
				createEntry("__FLT64_HAS_QUIET_NAN__", "1"), createEntry("__FLT64_MANT_DIG__", "53"),
				createEntry("__FLT64_MAX_10_EXP__", "308"), createEntry("__FLT64_MAX_EXP__", "1024"),
				createEntry("__FLT64_MAX__", "1.79769313486231570814527423731704357e+308F64"),
				createEntry("__FLT64_MIN_10_EXP__", "(-307)"), createEntry("__FLT64_MIN_EXP__", "(-1021)"),
				createEntry("__FLT64_MIN__", "2.22507385850720138309023271733240406e-308F64"),
				createEntry("__FLT_DECIMAL_DIG__", "9"),
				createEntry("__FLT_DENORM_MIN__", "1.40129846432481707092372958328991613e-45F"),
				createEntry("__FLT_DIG__", "6"),
				createEntry("__FLT_EPSILON__", "1.19209289550781250000000000000000000e-7F"),
				createEntry("__FLT_EVAL_METHOD_TS_18661_3__", "0"), createEntry("__FLT_EVAL_METHOD__", "0"),
				createEntry("__FLT_HAS_DENORM__", "1"), createEntry("__FLT_HAS_INFINITY__", "1"),
				createEntry("__FLT_HAS_QUIET_NAN__", "1"), createEntry("__FLT_MANT_DIG__", "24"),
				createEntry("__FLT_MAX_10_EXP__", "38"), createEntry("__FLT_MAX_EXP__", "128"),
				createEntry("__FLT_MAX__", "3.40282346638528859811704183484516925e+38F"),
				createEntry("__FLT_MIN_10_EXP__", "(-37)"), createEntry("__FLT_MIN_EXP__", "(-125)"),
				createEntry("__FLT_MIN__", "1.17549435082228750796873653722224568e-38F"),
				createEntry("__FLT_RADIX__", "2"), createEntry("__FXSR__", "1"),
				createEntry("__GCC_ASM_FLAG_OUTPUTS__", "1"), createEntry("__GCC_ATOMIC_BOOL_LOCK_FREE", "2"),
				createEntry("__GCC_ATOMIC_CHAR16_T_LOCK_FREE", "2"),
				createEntry("__GCC_ATOMIC_CHAR32_T_LOCK_FREE", "2"), createEntry("__GCC_ATOMIC_CHAR_LOCK_FREE", "2"),
				createEntry("__GCC_ATOMIC_INT_LOCK_FREE", "2"), createEntry("__GCC_ATOMIC_LLONG_LOCK_FREE", "2"),
				createEntry("__GCC_ATOMIC_LONG_LOCK_FREE", "2"), createEntry("__GCC_ATOMIC_POINTER_LOCK_FREE", "2"),
				createEntry("__GCC_ATOMIC_SHORT_LOCK_FREE", "2"), createEntry("__GCC_ATOMIC_TEST_AND_SET_TRUEVAL", "1"),
				createEntry("__GCC_ATOMIC_WCHAR_T_LOCK_FREE", "2"),
				createEntry("__GCC_HAVE_SYNC_COMPARE_AND_SWAP_1", "1"),
				createEntry("__GCC_HAVE_SYNC_COMPARE_AND_SWAP_16", "1"),
				createEntry("__GCC_HAVE_SYNC_COMPARE_AND_SWAP_2", "1"),
				createEntry("__GCC_HAVE_SYNC_COMPARE_AND_SWAP_4", "1"),
				createEntry("__GCC_HAVE_SYNC_COMPARE_AND_SWAP_8", "1"), createEntry("__GCC_IEC_559", "2"),
				createEntry("__GCC_IEC_559_COMPLEX", "2"), createEntry("__GNUC_MINOR__", "3"),
				createEntry("__GNUC_PATCHLEVEL__", "0"), createEntry("__GNUC_STDC_INLINE__", "1"),
				createEntry("__GNUC__", "8"), createEntry("__GXX_ABI_VERSION", "1013"),
				createEntry("__GXX_MERGED_TYPEINFO_NAMES", "0"), createEntry("__GXX_TYPEINFO_EQUALITY_INLINE", "0"),
				createEntry("__INT16_C(c)", "c"), createEntry("__INT16_MAX__", "0x7fff"),
				createEntry("__INT16_TYPE__", "short int"), createEntry("__INT32_C(c)", "c"),
				createEntry("__INT32_MAX__", "0x7fffffff"), createEntry("__INT32_TYPE__", "int"),
				createEntry("__INT64_C(c)", "c ## LL"), createEntry("__INT64_MAX__", "0x7fffffffffffffffLL"),
				createEntry("__INT64_TYPE__", "long long int"), createEntry("__INT8_C(c)", "c"),
				createEntry("__INT8_MAX__", "0x7f"), createEntry("__INT8_TYPE__", "signed char"),
				createEntry("__INTMAX_C(c)", "c ## LL"), createEntry("__INTMAX_MAX__", "0x7fffffffffffffffLL"),
				createEntry("__INTMAX_TYPE__", "long long int"), createEntry("__INTMAX_WIDTH__", "64"),
				createEntry("__INTPTR_MAX__", "0x7fffffffffffffffLL"), createEntry("__INTPTR_TYPE__", "long long int"),
				createEntry("__INTPTR_WIDTH__", "64"), createEntry("__INT_FAST16_MAX__", "0x7fff"),
				createEntry("__INT_FAST16_TYPE__", "short int"), createEntry("__INT_FAST16_WIDTH__", "16"),
				createEntry("__INT_FAST32_MAX__", "0x7fffffff"), createEntry("__INT_FAST32_TYPE__", "int"),
				createEntry("__INT_FAST32_WIDTH__", "32"), createEntry("__INT_FAST64_MAX__", "0x7fffffffffffffffLL"),
				createEntry("__INT_FAST64_TYPE__", "long long int"), createEntry("__INT_FAST64_WIDTH__", "64"),
				createEntry("__INT_FAST8_MAX__", "0x7f"), createEntry("__INT_FAST8_TYPE__", "signed char"),
				createEntry("__INT_FAST8_WIDTH__", "8"), createEntry("__INT_LEAST16_MAX__", "0x7fff"),
				createEntry("__INT_LEAST16_TYPE__", "short int"), createEntry("__INT_LEAST16_WIDTH__", "16"),
				createEntry("__INT_LEAST32_MAX__", "0x7fffffff"), createEntry("__INT_LEAST32_TYPE__", "int"),
				createEntry("__INT_LEAST32_WIDTH__", "32"), createEntry("__INT_LEAST64_MAX__", "0x7fffffffffffffffLL"),
				createEntry("__INT_LEAST64_TYPE__", "long long int"), createEntry("__INT_LEAST64_WIDTH__", "64"),
				createEntry("__INT_LEAST8_MAX__", "0x7f"), createEntry("__INT_LEAST8_TYPE__", "signed char"),
				createEntry("__INT_LEAST8_WIDTH__", "8"), createEntry("__INT_MAX__", "0x7fffffff"),
				createEntry("__INT_WIDTH__", "32"), createEntry("__LDBL_DECIMAL_DIG__", "21"),
				createEntry("__LDBL_DENORM_MIN__", "3.64519953188247460252840593361941982e-4951L"),
				createEntry("__LDBL_DIG__", "18"),
				createEntry("__LDBL_EPSILON__", "1.08420217248550443400745280086994171e-19L"),
				createEntry("__LDBL_HAS_DENORM__", "1"), createEntry("__LDBL_HAS_INFINITY__", "1"),
				createEntry("__LDBL_HAS_QUIET_NAN__", "1"), createEntry("__LDBL_MANT_DIG__", "64"),
				createEntry("__LDBL_MAX_10_EXP__", "4932"), createEntry("__LDBL_MAX_EXP__", "16384"),
				createEntry("__LDBL_MAX__", "1.18973149535723176502126385303097021e+4932L"),
				createEntry("__LDBL_MIN_10_EXP__", "(-4931)"), createEntry("__LDBL_MIN_EXP__", "(-16381)"),
				createEntry("__LDBL_MIN__", "3.36210314311209350626267781732175260e-4932L"),
				createEntry("__LONG_LONG_MAX__", "0x7fffffffffffffffLL"), createEntry("__LONG_LONG_WIDTH__", "64"),
				createEntry("__LONG_MAX__", "0x7fffffffL"), createEntry("__LONG_WIDTH__", "32"),
				createEntry("__MINGW32__", "1"), createEntry("__MINGW64__", "1"), createEntry("__MMX__", "1"),
				createEntry("__MSVCRT__", "1"), createEntry("__NO_INLINE__", "1"),
				createEntry("__ORDER_BIG_ENDIAN__", "4321"), createEntry("__ORDER_LITTLE_ENDIAN__", "1234"),
				createEntry("__ORDER_PDP_ENDIAN__", "3412"), createEntry("__PIC__", "1"),
				createEntry("__PRAGMA_REDEFINE_EXTNAME", "1"), createEntry("__PTRDIFF_MAX__", "0x7fffffffffffffffLL"),
				createEntry("__PTRDIFF_TYPE__", "long long int"), createEntry("__PTRDIFF_WIDTH__", "64"),
				createEntry("__REGISTER_PREFIX__", ""), createEntry("__SCHAR_MAX__", "0x7f"),
				createEntry("__SCHAR_WIDTH__", "8"), createEntry("__SEG_FS", "1"), createEntry("__SEG_GS", "1"),
				createEntry("__SEH__", "1"), createEntry("__SHRT_MAX__", "0x7fff"), createEntry("__SHRT_WIDTH__", "16"),
				createEntry("__SIG_ATOMIC_MAX__", "0x7fffffff"),
				createEntry("__SIG_ATOMIC_MIN__", "(-__SIG_ATOMIC_MAX__ - 1)"),
				createEntry("__SIG_ATOMIC_TYPE__", "int"), createEntry("__SIG_ATOMIC_WIDTH__", "32"),
				createEntry("__SIZEOF_DOUBLE__", "8"), createEntry("__SIZEOF_FLOAT128__", "16"),
				createEntry("__SIZEOF_FLOAT80__", "16"), createEntry("__SIZEOF_FLOAT__", "4"),
				createEntry("__SIZEOF_INT128__", "16"), createEntry("__SIZEOF_INT__", "4"),
				createEntry("__SIZEOF_LONG_DOUBLE__", "16"), createEntry("__SIZEOF_LONG_LONG__", "8"),
				createEntry("__SIZEOF_LONG__", "4"), createEntry("__SIZEOF_POINTER__", "8"),
				createEntry("__SIZEOF_PTRDIFF_T__", "8"), createEntry("__SIZEOF_SHORT__", "2"),
				createEntry("__SIZEOF_SIZE_T__", "8"), createEntry("__SIZEOF_WCHAR_T__", "2"),
				createEntry("__SIZEOF_WINT_T__", "2"), createEntry("__SIZE_MAX__", "0xffffffffffffffffULL"),
				createEntry("__SIZE_TYPE__", "long long unsigned int"), createEntry("__SIZE_WIDTH__", "64"),
				createEntry("__SSE2_MATH__", "1"), createEntry("__SSE2__", "1"), createEntry("__SSE3__", "1"),
				createEntry("__SSE_MATH__", "1"), createEntry("__SSE__", "1"), createEntry("__STDC_HOSTED__", "1"),
				createEntry("__STDC_UTF_16__", "1"), createEntry("__STDC_UTF_32__", "1"),
				createEntry("__STDC_VERSION__", "201710L"), createEntry("__STDC__", "1"),
				createEntry("__UINT16_C(c)", "c"), createEntry("__UINT16_MAX__", "0xffff"),
				createEntry("__UINT16_TYPE__", "short unsigned int"), createEntry("__UINT32_C(c)", "c ## U"),
				createEntry("__UINT32_MAX__", "0xffffffffU"), createEntry("__UINT32_TYPE__", "unsigned int"),
				createEntry("__UINT64_C(c)", "c ## ULL"), createEntry("__UINT64_MAX__", "0xffffffffffffffffULL"),
				createEntry("__UINT64_TYPE__", "long long unsigned int"), createEntry("__UINT8_C(c)", "c"),
				createEntry("__UINT8_MAX__", "0xff"), createEntry("__UINT8_TYPE__", "unsigned char"),
				createEntry("__UINTMAX_C(c)", "c ## ULL"), createEntry("__UINTMAX_MAX__", "0xffffffffffffffffULL"),
				createEntry("__UINTMAX_TYPE__", "long long unsigned int"),
				createEntry("__UINTPTR_MAX__", "0xffffffffffffffffULL"),
				createEntry("__UINTPTR_TYPE__", "long long unsigned int"), createEntry("__UINT_FAST16_MAX__", "0xffff"),
				createEntry("__UINT_FAST16_TYPE__", "short unsigned int"),
				createEntry("__UINT_FAST32_MAX__", "0xffffffffU"), createEntry("__UINT_FAST32_TYPE__", "unsigned int"),
				createEntry("__UINT_FAST64_MAX__", "0xffffffffffffffffULL"),
				createEntry("__UINT_FAST64_TYPE__", "long long unsigned int"),
				createEntry("__UINT_FAST8_MAX__", "0xff"), createEntry("__UINT_FAST8_TYPE__", "unsigned char"),
				createEntry("__UINT_LEAST16_MAX__", "0xffff"),
				createEntry("__UINT_LEAST16_TYPE__", "short unsigned int"),
				createEntry("__UINT_LEAST32_MAX__", "0xffffffffU"),
				createEntry("__UINT_LEAST32_TYPE__", "unsigned int"),
				createEntry("__UINT_LEAST64_MAX__", "0xffffffffffffffffULL"),
				createEntry("__UINT_LEAST64_TYPE__", "long long unsigned int"),
				createEntry("__UINT_LEAST8_MAX__", "0xff"), createEntry("__UINT_LEAST8_TYPE__", "unsigned char"),
				createEntry("__USER_LABEL_PREFIX__", ""), createEntry("__WCHAR_MAX__", "0xffff"),
				createEntry("__WCHAR_MIN__", "0"), createEntry("__WCHAR_TYPE__", "short unsigned int"),
				createEntry("__WCHAR_WIDTH__", "16"), createEntry("__WIN32", "1"), createEntry("__WIN32__", "1"),
				createEntry("__WIN64", "1"), createEntry("__WIN64__", "1"), createEntry("__WINNT", "1"),
				createEntry("__WINNT__", "1"), createEntry("__WINT_MAX__", "0xffff"), createEntry("__WINT_MIN__", "0"),
				createEntry("__WINT_TYPE__", "short unsigned int"), createEntry("__WINT_WIDTH__", "16"),
				createEntry("__amd64", "1"), createEntry("__amd64__", "1"),
				createEntry("__cdecl", "__attribute__((__cdecl__))"), createEntry("__code_model_medium__", "1"),
				createEntry("__declspec(x)", "__attribute__((x))"),
				createEntry("__fastcall", "__attribute__((__fastcall__))"),
				createEntry("__has_include(STR)", "__has_include__(STR)"),
				createEntry("__has_include_next(STR)", "__has_include_next__(STR)"), createEntry("__nocona", "1"),
				createEntry("__nocona__", "1"), createEntry("__pic__", "1"),
				createEntry("__stdcall", "__attribute__((__stdcall__))"),
				createEntry("__thiscall", "__attribute__((__thiscall__))"), createEntry("__tune_core2__", "1"),
				createEntry("__x86_64", "1"), createEntry("__x86_64__", "1"),
				createEntry("_cdecl", "__attribute__((__cdecl__))"),
				createEntry("_fastcall", "__attribute__((__fastcall__))"),
				createEntry("_stdcall", "__attribute__((__stdcall__))"),
				createEntry("_thiscall", "__attribute__((__thiscall__))"),
				createEntry("__builtin_va_arg(ap,type)", "*((typeof(type) *)((ap += sizeof(type)) - sizeof(type)))"),
				createEntry("__thread", "__attribute__((thread))"),
				createEntry("thread_local", "__attribute__((thread))") };

		mSettings = LanguageSettingsStorage.getPooledList(Arrays.asList(entries));

	}

	@Override
	public String getId() {
		return GccStaticLanguageSettingsProvider.class.getName();
	}

	@Override
	public String getName() {
		return GccStaticLanguageSettingsProvider.class.getSimpleName();
	}

	private static ICLanguageSettingEntry createEntry(final String name, final String value) {
		return new CMacroEntry(name, value, ICSettingEntry.BUILTIN | ICSettingEntry.READONLY);
	}

	@Override
	public List<ICLanguageSettingEntry> getSettingEntries(final ICConfigurationDescription cfgDescription,
			final IResource rc, final String languageId) {
		return mSettings;
	}

}
