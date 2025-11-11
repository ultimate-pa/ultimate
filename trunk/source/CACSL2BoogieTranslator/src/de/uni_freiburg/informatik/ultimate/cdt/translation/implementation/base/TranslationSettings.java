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

import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.CheckMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.FloatingPointRoundingMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.MemoryModel;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerIntegerConversion;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.UndefinedFunctionBehaviour;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public final class TranslationSettings {
	private final CheckMode mDivisionByZeroOfIntegerTypes;
	private final CheckMode mDivisionByZeroOfFloatingTypes;
	private final boolean mBitvectorTranslation;
	private final boolean mOverapproximateFloatingPointOperations;
	private final boolean mBitpreciseBitfields;
	private final boolean mInRange;
	private final PointerIntegerConversion mPointerIntegerConversion;
	private final boolean mCheckIfFreedPointerIsValid;
	private final CheckMode mCheckPointerDerefValidity;
	private final CheckMode mCheckPointerSubtractionAndComparisonValidity;
	/**
	 * List of functions for which we check memory-neutrality.
	 */
	private final Set<String> mFunctionsCheckedForMemoryNeutrality;
	private final MemoryModel mMemoryModelPreference;
	private final boolean mFpToIeeeBvExtension;
	private final boolean mSmtBoolArraysWorkaround;
	private final String mEntryFunction;
	private final boolean mCheckErrorFunction;
	private final boolean mCheckAssertions;
	private final boolean mCheckAcsl;
	private final boolean mIsSvcompMemtrackCompatibilityMode;
	private final CheckMode mCheckSignedIntegerBounds;
	private final boolean mCheckDataRaces;
	private final boolean mUseConstantArrays;
	private final boolean mUseStoreChains;
	private final boolean mEnableFesetround;
	private final FloatingPointRoundingMode mInitialRoundingMode;
	private final boolean mAdaptMemoryModelResolutionOnPointerCasts;
	private final int mStringOverapproximationThreshold;
	private final UndefinedFunctionBehaviour mUndefinedFunctionBehaviour;
	private final boolean mEnforceIfForConditional;

	public TranslationSettings(final IPreferenceProvider ups) {
		mCheckSignedIntegerBounds =
				ups.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_SIGNED_INTEGER_BOUNDS, CheckMode.class);
		mCheckDataRaces = ups.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_DATA_RACES);
		mIsSvcompMemtrackCompatibilityMode =
				ups.getBoolean(CACSLPreferenceInitializer.LABEL_SVCOMP_MEMTRACK_COMPATIBILITY_MODE);

		mCheckAssertions = ups.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_ASSERTIONS);
		mCheckAcsl = ups.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_ACSL);
		mEntryFunction = ups.getString(CACSLPreferenceInitializer.MAINPROC_LABEL);
		mCheckErrorFunction = ups.getBoolean(CACSLPreferenceInitializer.LABEL_ERROR);
		mSmtBoolArraysWorkaround = ups.getBoolean(CACSLPreferenceInitializer.LABEL_SMT_BOOL_ARRAYS_WORKAROUND);
		mCheckIfFreedPointerIsValid = ups.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_FREE_VALID);
		mCheckPointerDerefValidity =
				ups.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_DEREF_VALIDITY, CheckMode.class);
		mCheckPointerSubtractionAndComparisonValidity = ups.getEnum(
				CACSLPreferenceInitializer.LABEL_CHECK_POINTER_SUBTRACTION_AND_COMPARISON_VALIDITY, CheckMode.class);
		{
			final String commaSeparatedSequence =
					ups.getString(CACSLPreferenceInitializer.LABEL_CHECK_MEMORY_NEUTRALITY);
			// Replace each sequence of whitespaces by the empty string
			final String withoutWhitespaces = commaSeparatedSequence.replaceAll("\\s+", "");
			if (withoutWhitespaces.isEmpty()) {
				mFunctionsCheckedForMemoryNeutrality = Set.of();
			} else {
				mFunctionsCheckedForMemoryNeutrality = Set.of(withoutWhitespaces.split(","));
			}
		}
		mMemoryModelPreference = ups.getEnum(CACSLPreferenceInitializer.LABEL_MEMORY_MODEL, MemoryModel.class);
		mFpToIeeeBvExtension = ups.getBoolean(CACSLPreferenceInitializer.LABEL_FP_TO_IEEE_BV_EXTENSION);

		mPointerIntegerConversion = ups.getEnum(CACSLPreferenceInitializer.LABEL_POINTER_INTEGER_CONVERSION,
				CACSLPreferenceInitializer.PointerIntegerConversion.class);
		mInRange = ups.getBoolean(CACSLPreferenceInitializer.LABEL_ASSUME_NONDET_VALUES_IN_RANGE);
		mDivisionByZeroOfIntegerTypes =
				ups.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_DIVISION_BY_ZERO_OF_INTEGER_TYPES, CheckMode.class);
		mDivisionByZeroOfFloatingTypes =
				ups.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_DIVISION_BY_ZERO_OF_FLOATING_TYPES, CheckMode.class);
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
		mUndefinedFunctionBehaviour = ups.getEnum(CACSLPreferenceInitializer.LABEL_BEHAVIOUR_UNDEFINED_FUNCTIONS,
				CACSLPreferenceInitializer.UndefinedFunctionBehaviour.class);
		mEnforceIfForConditional = ups.getBoolean(CACSLPreferenceInitializer.LABEL_ENFORCE_IF_FOR_CONDITIONAL);
	}

	private TranslationSettings(final CheckMode divisionByZeroOfIntegerTypes,
			final CheckMode divisionByZeroOfFloatingTypes, final boolean bitvectorTranslation,
			final boolean overapproximateFloatingPointOperations, final boolean bitpreciseBitfields,
			final boolean inRange, final PointerIntegerConversion pointerIntegerConversion,
			final boolean checkIfFreedPointerIsValid, final CheckMode checkPointerDerefValidity,
			final CheckMode checkPointerSubtractionAndComparisonValidity, final MemoryModel memoryModelPreference,
			final boolean fpToIeeeBvExtension, final boolean smtBoolArraysWorkaround, final String entryFunction,
			final boolean checkErrorFunction, final boolean checkAssertions, final boolean checkAcsl,
			final boolean isSvcompMemtrackCompatibilityMode, final Set<String> functionsCheckedForMemoryNeutrality,
			final CheckMode checkSignedIntegerBounds, final boolean checkDataRaces, final boolean useConstantArrays,
			final boolean useStoreChains, final boolean enableFesetround,
			final FloatingPointRoundingMode initialRoundingMode, final boolean adaptMemoryModelResolutionOnPointerCasts,
			final int stringOverapproximationThreshold, final UndefinedFunctionBehaviour undefinedFunctionBehaviour,
			final boolean enforceIfForConditional) {
		mDivisionByZeroOfIntegerTypes = divisionByZeroOfIntegerTypes;
		mDivisionByZeroOfFloatingTypes = divisionByZeroOfFloatingTypes;
		mBitvectorTranslation = bitvectorTranslation;
		mOverapproximateFloatingPointOperations = overapproximateFloatingPointOperations;
		mBitpreciseBitfields = bitpreciseBitfields;
		mInRange = inRange;
		mPointerIntegerConversion = pointerIntegerConversion;
		mCheckIfFreedPointerIsValid = checkIfFreedPointerIsValid;
		mCheckPointerDerefValidity = checkPointerDerefValidity;
		mCheckPointerSubtractionAndComparisonValidity = checkPointerSubtractionAndComparisonValidity;
		mMemoryModelPreference = memoryModelPreference;
		mFpToIeeeBvExtension = fpToIeeeBvExtension;
		mSmtBoolArraysWorkaround = smtBoolArraysWorkaround;
		mEntryFunction = entryFunction;
		mCheckErrorFunction = checkErrorFunction;
		mCheckAssertions = checkAssertions;
		mCheckAcsl = checkAcsl;
		mIsSvcompMemtrackCompatibilityMode = isSvcompMemtrackCompatibilityMode;
		mFunctionsCheckedForMemoryNeutrality = functionsCheckedForMemoryNeutrality;
		mCheckSignedIntegerBounds = checkSignedIntegerBounds;
		mCheckDataRaces = checkDataRaces;
		mUseConstantArrays = useConstantArrays;
		mUseStoreChains = useStoreChains;
		mEnableFesetround = enableFesetround;
		mInitialRoundingMode = initialRoundingMode;
		mAdaptMemoryModelResolutionOnPointerCasts = adaptMemoryModelResolutionOnPointerCasts;
		mStringOverapproximationThreshold = stringOverapproximationThreshold;
		mUndefinedFunctionBehaviour = undefinedFunctionBehaviour;
		mEnforceIfForConditional = enforceIfForConditional;
	}

	public PointerIntegerConversion getPointerIntegerCastMode() {
		return mPointerIntegerConversion;
	}

	public boolean assumeNondeterministicValuesInRange() {
		return mInRange;
	}

	public CheckMode getDivisionByZeroOfIntegerTypes() {
		return mDivisionByZeroOfIntegerTypes;
	}

	public CheckMode getDivisionByZeroOfFloatingTypes() {
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

	public CheckMode checkPointerDerefValidity() {
		return mCheckPointerDerefValidity;
	}

	public boolean checkIfFreedPointerIsValid() {
		return mCheckIfFreedPointerIsValid;
	}

	public CheckMode getPointerSubtractionAndComparisonValidityCheckMode() {
		return mCheckPointerSubtractionAndComparisonValidity;
	}

	public boolean useSmtBoolArrayWorkaround() {
		return mSmtBoolArraysWorkaround;
	}

	public String getEntryFunction() {
		return mEntryFunction;
	}

	public boolean checkErrorFunction() {
		return mCheckErrorFunction;
	}

	public boolean checkAssertions() {
		return mCheckAssertions;
	}

	public boolean checkAcsl() {
		return mCheckAcsl;
	}

	public boolean isSvcompMemtrackCompatibilityMode() {
		return mIsSvcompMemtrackCompatibilityMode;
	}

	public Set<String> getFunctionsCheckedForMemoryNeutrality() {
		return mFunctionsCheckedForMemoryNeutrality;
	}

	public CheckMode checkSignedIntegerBounds() {
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

	public UndefinedFunctionBehaviour getUndefinedFunctionBehaviour() {
		return mUndefinedFunctionBehaviour;
	}

	public boolean enforceIfForConditional() {
		return mEnforceIfForConditional;
	}

	public TranslationSettings setMemoryModelPreference(final MemoryModel memoryModel) {
		return new TranslationSettings(mDivisionByZeroOfIntegerTypes, mDivisionByZeroOfFloatingTypes,
				mBitvectorTranslation, mOverapproximateFloatingPointOperations, mBitpreciseBitfields, mInRange,
				mPointerIntegerConversion, mCheckIfFreedPointerIsValid, mCheckPointerDerefValidity,
				mCheckPointerSubtractionAndComparisonValidity, memoryModel, mFpToIeeeBvExtension,
				mSmtBoolArraysWorkaround, mEntryFunction, mCheckErrorFunction, mCheckAssertions, mCheckAcsl,
				mIsSvcompMemtrackCompatibilityMode, mFunctionsCheckedForMemoryNeutrality, mCheckSignedIntegerBounds, mCheckDataRaces,
				mUseConstantArrays, mUseStoreChains, mEnableFesetround, mInitialRoundingMode,
				mAdaptMemoryModelResolutionOnPointerCasts, mStringOverapproximationThreshold,
				mUndefinedFunctionBehaviour, mEnforceIfForConditional);
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
			return Objects.hash(mNewPreferredMemoryModel);
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
