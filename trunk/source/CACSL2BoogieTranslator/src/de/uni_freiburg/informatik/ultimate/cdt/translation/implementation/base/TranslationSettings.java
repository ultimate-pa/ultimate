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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.FloatingPointRoundingMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.MemoryModel;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerCheckMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerIntegerConversion;

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
	private final boolean mInRange;
	private final PointerIntegerConversion mPointerIntegerConversion;
	private final boolean mCheckIfFreedPointerIsValid;
	private final PointerCheckMode mPointerBaseValidity;
	private final PointerCheckMode mPointerTargetFullyAllocated;
	private final PointerCheckMode mCheckPointerSubtractionAndComparisonValidity;
	private final MemoryModel mMemoryModelPreference;
	private final boolean mFpToIeeeBvExtension;
	private final boolean mSmtBoolArraysWorkaround;
	private final String mEntryMethod;
	private final boolean mCheckErrorFunction;
	private final boolean mCheckAssertions;
	private final boolean mIsSvcompMemtrackCompatibilityMode;
	private final boolean mCheckAllocationPurity;
	private final boolean mCheckMemoryLeakInMain;
	private final boolean mCheckSignedIntegerBounds;
	private final boolean mCheckDataRaces;
	private final boolean mUseConstantArrays;
	private final boolean mUseStoreChains;
	private final boolean mEnableFesetround;
	private final FloatingPointRoundingMode mInitialRoundingMode;
	private final boolean mAdaptMemoryModelResolutionOnPointerCasts;
	private final int mStringOverapproximationThreshold;
	private boolean mAllowUndefinedFunctions;

	public TranslationSettings(final IPreferenceProvider ups) {
		mCheckSignedIntegerBounds = ups.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_SIGNED_INTEGER_BOUNDS);
		mCheckDataRaces = ups.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_DATA_RACES);
		mIsSvcompMemtrackCompatibilityMode =
				ups.getBoolean(CACSLPreferenceInitializer.LABEL_SVCOMP_MEMTRACK_COMPATIBILITY_MODE);
		mCheckAllocationPurity = ups.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_ALLOCATION_PURITY);
		mCheckMemoryLeakInMain = ups.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_MEMORY_LEAK_IN_MAIN);

		mCheckAssertions = ups.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_ASSERTIONS);
		mEntryMethod = ups.getString(CACSLPreferenceInitializer.MAINPROC_LABEL);
		mCheckErrorFunction = ups.getBoolean(CACSLPreferenceInitializer.LABEL_ERROR);
		mSmtBoolArraysWorkaround = ups.getBoolean(CACSLPreferenceInitializer.LABEL_SMT_BOOL_ARRAYS_WORKAROUND);
		mCheckIfFreedPointerIsValid = ups.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_FREE_VALID);
		mPointerBaseValidity =
				ups.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_VALIDITY, PointerCheckMode.class);
		mPointerTargetFullyAllocated =
				ups.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_ALLOC, PointerCheckMode.class);
		// mCheckFreeValid =
		// prefs.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_FREE_VALID);
		mCheckPointerSubtractionAndComparisonValidity =
				ups.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_SUBTRACTION_AND_COMPARISON_VALIDITY,
						PointerCheckMode.class);
		mMemoryModelPreference = ups.getEnum(CACSLPreferenceInitializer.LABEL_MEMORY_MODEL, MemoryModel.class);
		mFpToIeeeBvExtension = ups.getBoolean(CACSLPreferenceInitializer.LABEL_FP_TO_IEEE_BV_EXTENSION);

		mPointerIntegerConversion = ups.getEnum(CACSLPreferenceInitializer.LABEL_POINTER_INTEGER_CONVERSION,
				CACSLPreferenceInitializer.PointerIntegerConversion.class);
		mInRange = ups.getBoolean(CACSLPreferenceInitializer.LABEL_ASSUME_NONDET_VALUES_IN_RANGE);
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
		mAdaptMemoryModelResolutionOnPointerCasts =
				ups.getBoolean(CACSLPreferenceInitializer.LABEL_ADAPT_MEMORY_MODEL_ON_POINTER_CASTS);
		mStringOverapproximationThreshold =
				ups.getInt(CACSLPreferenceInitializer.LABEL_STRING_OVERAPPROXIMATION_THRESHOLD);
		mAllowUndefinedFunctions = ups.getBoolean(CACSLPreferenceInitializer.LABEL_ALLOW_UNDEFINED_FUNCTIONS);
	}

	private TranslationSettings(final PointerCheckMode divisionByZeroOfIntegerTypes,
			final PointerCheckMode divisionByZeroOfFloatingTypes, final boolean bitvectorTranslation,
			final boolean overapproximateFloatingPointOperations, final boolean bitpreciseBitfields,
			final PointerCheckMode checkArrayAccessOffHeap, final boolean inRange,
			final PointerIntegerConversion pointerIntegerConversion, final boolean checkIfFreedPointerIsValid,
			final PointerCheckMode pointerBaseValidity, final PointerCheckMode pointerTargetFullyAllocated,
			final PointerCheckMode checkPointerSubtractionAndComparisonValidity,
			final MemoryModel memoryModelPreference, final boolean fpToIeeeBvExtension,
			final boolean smtBoolArraysWorkaround, final String checkedMethod, final boolean checkErrorFunction,
			final boolean checkSvcompErrorFunction, final boolean isSvcompMemtrackCompatibilityMode,
			final boolean checkAllocationPurity, final boolean checkMemoryLeakInMain,
			final boolean checkSignedIntegerBounds, final boolean checkDataRaces, final boolean useConstantArrays,
			final boolean useStoreChains, final boolean enableFesetround,
			final FloatingPointRoundingMode initialRoundingMode, final boolean adaptMemoryModelResolutionOnPointerCasts,
			final int stringOverapproximationThreshold) {
		mDivisionByZeroOfIntegerTypes = divisionByZeroOfIntegerTypes;
		mDivisionByZeroOfFloatingTypes = divisionByZeroOfFloatingTypes;
		mBitvectorTranslation = bitvectorTranslation;
		mOverapproximateFloatingPointOperations = overapproximateFloatingPointOperations;
		mBitpreciseBitfields = bitpreciseBitfields;
		mCheckArrayAccessOffHeap = checkArrayAccessOffHeap;
		mInRange = inRange;
		mPointerIntegerConversion = pointerIntegerConversion;
		mCheckIfFreedPointerIsValid = checkIfFreedPointerIsValid;
		mPointerBaseValidity = pointerBaseValidity;
		mPointerTargetFullyAllocated = pointerTargetFullyAllocated;
		mCheckPointerSubtractionAndComparisonValidity = checkPointerSubtractionAndComparisonValidity;
		mMemoryModelPreference = memoryModelPreference;
		mFpToIeeeBvExtension = fpToIeeeBvExtension;
		mSmtBoolArraysWorkaround = smtBoolArraysWorkaround;
		mEntryMethod = checkedMethod;
		mCheckErrorFunction = checkErrorFunction;
		mCheckAssertions = checkSvcompErrorFunction;
		mIsSvcompMemtrackCompatibilityMode = isSvcompMemtrackCompatibilityMode;
		mCheckAllocationPurity = checkAllocationPurity;
		mCheckMemoryLeakInMain = checkMemoryLeakInMain;
		mCheckSignedIntegerBounds = checkSignedIntegerBounds;
		mCheckDataRaces = checkDataRaces;
		mUseConstantArrays = useConstantArrays;
		mUseStoreChains = useStoreChains;
		mEnableFesetround = enableFesetround;
		mInitialRoundingMode = initialRoundingMode;
		mAdaptMemoryModelResolutionOnPointerCasts = adaptMemoryModelResolutionOnPointerCasts;
		mStringOverapproximationThreshold = stringOverapproximationThreshold;
	}

	public PointerIntegerConversion getPointerIntegerCastMode() {
		return mPointerIntegerConversion;
	}

	public boolean assumeNondeterministicValuesInRange() {
		return mInRange;
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

	public String getEntryMethod() {
		return mEntryMethod;
	}

	public boolean checkErrorFunction() {
		return mCheckErrorFunction;
	}

	public boolean checkAssertions() {
		return mCheckAssertions;
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

	public boolean checkDataRaces() {
		return mCheckDataRaces;
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

	public boolean isAdaptMemoryModelResolutionOnPointerCasts() {
		return mAdaptMemoryModelResolutionOnPointerCasts;
	}

	public int getStringOverapproximationThreshold() {
		return mStringOverapproximationThreshold;
	}

	public boolean allowUndefinedFunctions() {
		return mAllowUndefinedFunctions;
	}

	public TranslationSettings setMemoryModelPreference(final MemoryModel memoryModel) {
		return new TranslationSettings(mDivisionByZeroOfIntegerTypes, mDivisionByZeroOfFloatingTypes,
				mBitvectorTranslation, mOverapproximateFloatingPointOperations, mBitpreciseBitfields,
				mCheckArrayAccessOffHeap, mInRange, mPointerIntegerConversion, mCheckIfFreedPointerIsValid,
				mPointerBaseValidity, mPointerTargetFullyAllocated, mCheckPointerSubtractionAndComparisonValidity,
				memoryModel, mFpToIeeeBvExtension, mSmtBoolArraysWorkaround, mEntryMethod, mCheckErrorFunction,
				mCheckAssertions, mIsSvcompMemtrackCompatibilityMode, mCheckAllocationPurity, mCheckMemoryLeakInMain,
				mCheckSignedIntegerBounds, mCheckDataRaces, mUseConstantArrays, mUseStoreChains, mEnableFesetround,
				mInitialRoundingMode, mAdaptMemoryModelResolutionOnPointerCasts, mStringOverapproximationThreshold);
	}

	/**
	 * Represents an update that is to be made to a {@link TranslationSettings} object.
	 *
	 * Currently this only supports one kind of settings change, namely one to the memory model. Extend it on demand..
	 *
	 * @author nutz@informatik.uni-freiburg.de
	 */
	public final static class SettingsChange {

		private final MemoryModel mNewPreferredMemoryModel;
		private final ILocation mLoc;
		private final String mMsg;

		public SettingsChange(final ILocation loc, final String msg, final MemoryModel newPreferredMemoryModel) {
			mNewPreferredMemoryModel = newPreferredMemoryModel;
			mLoc = loc;
			mMsg = msg;
		}

		public TranslationSettings applyChangeTo(final TranslationSettings oldSettings) {
			return oldSettings.setMemoryModelPreference(mNewPreferredMemoryModel);
		}

		public UnsupportedSyntaxException constructException(final String reasonForThrowing) {
			return new UnsupportedSyntaxException(mLoc, mMsg + " (while " + reasonForThrowing + ")");
		}

		@Override
		public String toString() {
			return "SettingsChange [mNewPreferredMemoryModel=" + mNewPreferredMemoryModel + "]";
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((mNewPreferredMemoryModel == null) ? 0 : mNewPreferredMemoryModel.hashCode());
			return result;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final SettingsChange other = (SettingsChange) obj;
			if (mNewPreferredMemoryModel != other.mNewPreferredMemoryModel) {
				return false;
			}
			return true;
		}
	}
}