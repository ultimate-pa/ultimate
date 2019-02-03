/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Stefan Wissert
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.TranslationMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.FloatingPointRoundingMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.MemoryModel;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerCheckMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerIntegerConversion;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.UnsignedTreatment;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public final class TranslationSettings {
	private final PointerCheckMode mDivisionByZeroOfIntegerTypes;
	private final PointerCheckMode mDivisionByZeroOfFloatingTypes;
	private final boolean mBitvectorTranslation;
	private final boolean mOverapproximateFloatingPointOperations;
	private final boolean mBitpreciseBitfields;
	private final PointerCheckMode mCheckArrayAccessOffHeap;
	private final UnsignedTreatment mUnsignedTreatment;
	private final boolean mInRange;
	private final PointerIntegerConversion mPointerIntegerConversion;
	private final boolean mCheckIfFreedPointerIsValid;
	private final PointerCheckMode mPointerBaseValidity;
	private final PointerCheckMode mPointerTargetFullyAllocated;
	private final PointerCheckMode mCheckPointerSubtractionAndComparisonValidity;
	private final MemoryModel mMemoryModelPreference;
	private final boolean mFpToIeeeBvExtension;
	private final boolean mSmtBoolArraysWorkaround;
	private final String mCheckedMethod;
	private final TranslationMode mTranslationMode;
	private final boolean mCheckSvcompErrorFunction;
	private final boolean mIsSvcompMemtrackCompatibilityMode;
	private final boolean mCheckAllocationPurity;
	private final boolean mCheckMemoryLeakInMain;
	private final boolean mCheckSignedIntegerBounds;
	private final boolean mUseConstantArrays;
	private final boolean mUseStoreChains;
	private final boolean mEnableFesetround;
	private final FloatingPointRoundingMode mInitialRoundingMode;

	public TranslationSettings(final IPreferenceProvider ups) {
		mCheckSignedIntegerBounds = ups.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_SIGNED_INTEGER_BOUNDS);
		mIsSvcompMemtrackCompatibilityMode =
				ups.getBoolean(CACSLPreferenceInitializer.LABEL_SVCOMP_MEMTRACK_COMPATIBILITY_MODE);
		mCheckAllocationPurity = ups.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_ALLOCATION_PURITY);
		mCheckMemoryLeakInMain = ups.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_MEMORY_LEAK_IN_MAIN);

		mCheckSvcompErrorFunction = ups.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_SVCOMP_ERRORFUNCTION);
		mCheckedMethod = ups.getString(CACSLPreferenceInitializer.MAINPROC_LABEL);
		mTranslationMode = ups.getEnum(CACSLPreferenceInitializer.LABEL_MODE, TranslationMode.class);
		mSmtBoolArraysWorkaround = ups.getBoolean(CACSLPreferenceInitializer.LABEL_SMT_BOOL_ARRAYS_WORKAROUND);
		mCheckIfFreedPointerIsValid = ups.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_FREE_VALID);
		mPointerBaseValidity =
				ups.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_VALIDITY, PointerCheckMode.class);
		mPointerTargetFullyAllocated =
				ups.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_ALLOC, PointerCheckMode.class);
		// mCheckFreeValid = prefs.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_FREE_VALID);
		mCheckPointerSubtractionAndComparisonValidity =
				ups.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_SUBTRACTION_AND_COMPARISON_VALIDITY,
						PointerCheckMode.class);
		mMemoryModelPreference = ups.getEnum(CACSLPreferenceInitializer.LABEL_MEMORY_MODEL, MemoryModel.class);
		mFpToIeeeBvExtension = ups.getBoolean(CACSLPreferenceInitializer.LABEL_FP_TO_IEEE_BV_EXTENSION);

		mPointerIntegerConversion = ups.getEnum(CACSLPreferenceInitializer.LABEL_POINTER_INTEGER_CONVERSION,
				CACSLPreferenceInitializer.PointerIntegerConversion.class);
		mInRange = ups.getBoolean(CACSLPreferenceInitializer.LABEL_ASSUME_NONDET_VALUES_IN_RANGE);
		mUnsignedTreatment = ups.getEnum(CACSLPreferenceInitializer.LABEL_UNSIGNED_TREATMENT,
				CACSLPreferenceInitializer.UnsignedTreatment.class);
		mCheckArrayAccessOffHeap =
				ups.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_ARRAYACCESSOFFHEAP, PointerCheckMode.class);
		mDivisionByZeroOfIntegerTypes = ups.getEnum(
				CACSLPreferenceInitializer.LABEL_CHECK_DIVISION_BY_ZERO_OF_INTEGER_TYPES, PointerCheckMode.class);
		mDivisionByZeroOfFloatingTypes = ups.getEnum(
				CACSLPreferenceInitializer.LABEL_CHECK_DIVISION_BY_ZERO_OF_FLOATING_TYPES, PointerCheckMode.class);
		mBitpreciseBitfields = ups.getBoolean(CACSLPreferenceInitializer.LABEL_BITPRECISE_BITFIELDS);
		mBitvectorTranslation = ups.getBoolean(CACSLPreferenceInitializer.LABEL_BITVECTOR_TRANSLATION);
		mOverapproximateFloatingPointOperations =
				ups.getBoolean(CACSLPreferenceInitializer.LABEL_OVERAPPROXIMATE_FLOATS);
		mUseConstantArrays = ups.getBoolean(CACSLPreferenceInitializer.LABEL_USE_CONSTANT_ARRAYS);
		mUseStoreChains = ups.getBoolean(CACSLPreferenceInitializer.LABEL_USE_STORE_CHAINS);

		mEnableFesetround = ups.getBoolean(CACSLPreferenceInitializer.LABEL_FP_ROUNDING_MODE_ENABLE_FESETROUND);
		mInitialRoundingMode =
				ups.getEnum(CACSLPreferenceInitializer.LABEL_FP_ROUNDING_MODE_INITIAL, FloatingPointRoundingMode.class);
	}

	public PointerIntegerConversion getPointerIntegerCastMode() {
		return mPointerIntegerConversion;
	}

	public boolean assumeNondeterministicValuesInRange() {
		return mInRange;
	}

	public UnsignedTreatment unsignedTreatment() {
		return mUnsignedTreatment;
	}

	public PointerCheckMode checkArrayAccessOffHeap() {
		return mCheckArrayAccessOffHeap;
	}

	public PointerCheckMode getDivisionByZeroOfIntegerTypes() {
		return mDivisionByZeroOfIntegerTypes;
	}

	public PointerCheckMode getDivisionByZeroOfFloatingTypes() {
		return mDivisionByZeroOfFloatingTypes;
	}

	public CPrimitive getCTypeOfPointerComponents() {
		if (mBitvectorTranslation) {
			// 2015-10-29 Matthias: using int is unsound on 64bit systems, but it
			// probably saves a lot of conversions and I guess this unsoundness
			// is never a problem in the SV-COMP and most other code
			return new CPrimitive(CPrimitives.INT);
		}
		return new CPrimitive(CPrimitives.LONG);
	}

	/**
	 * if false we translate CPrimitives whose general type is INT to int. If true we translate CPrimitives whose
	 * general type is INT to identically named types,
	 */
	public boolean isBitvectorTranslation() {
		return mBitvectorTranslation;
	}

	public boolean overapproximateFloatingPointOperations() {
		return mOverapproximateFloatingPointOperations;
	}

	public boolean useBitpreciseBitfields() {
		return mBitpreciseBitfields;
	}

	public MemoryModel getMemoryModelPreference() {
		return mMemoryModelPreference;
	}

	public boolean useFpToIeeeBvExtension() {
		return mFpToIeeeBvExtension;
	}

	public PointerCheckMode getPointerTargetFullyAllocatedMode() {
		return mPointerTargetFullyAllocated;
	}

	public PointerCheckMode getPointerBaseValidityMode() {
		return mPointerBaseValidity;
	}

	public boolean checkIfFreedPointerIsValid() {
		return mCheckIfFreedPointerIsValid;
	}

	public PointerCheckMode getPointerSubtractionAndComparisonValidityCheckMode() {
		return mCheckPointerSubtractionAndComparisonValidity;
	}

	public boolean useSmtBoolArrayWorkaround() {
		return mSmtBoolArraysWorkaround;
	}

	public String getCheckedMethod() {
		return mCheckedMethod;
	}

	public boolean isSvcompMode() {
		switch (mTranslationMode) {
		case BASE:
			return false;
		case SV_COMP14:
			return true;
		default:
			throw new IllegalArgumentException("Unknown mode " + mTranslationMode);
		}
	}

	public boolean checkSvcompErrorFunction() {
		return mCheckSvcompErrorFunction;
	}

	public boolean isSvcompMemtrackCompatibilityMode() {
		return mIsSvcompMemtrackCompatibilityMode;
	}

	public boolean checkAllocationPurity() {
		return mCheckAllocationPurity;
	}

	public boolean checkMemoryLeakInMain() {
		return mCheckMemoryLeakInMain;
	}

	public boolean checkSignedIntegerBounds() {
		return mCheckSignedIntegerBounds;
	}

	public boolean useConstantArrays() {
		return mUseConstantArrays;
	}

	/**
	 * To recover the old behaviour (before SVCOMP-19), where initialization always happened through a list of
	 * assignments/stores (in contrast to the new assume-select strategy), set this to true.
	 */
	public boolean useStoreChains() {
		return mUseStoreChains;
	}

	public boolean isFesetroundEnabled() {
		return mEnableFesetround;
	}

	public FloatingPointRoundingMode getInitialRoundingMode() {
		return mInitialRoundingMode;
	}

}