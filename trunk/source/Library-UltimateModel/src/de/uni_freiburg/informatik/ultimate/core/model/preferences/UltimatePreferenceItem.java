/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.model.preferences;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.core.model.IController;

/**
 * An UltimatePReferenceItem describes exactly one setting of a preference. Based on its {@link PreferenceType}, the
 * active {@link IController} will present it to users for modification.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <T>
 *            The type of the preference. Usually a primitive, an enum, or something that can be easily constructed from
 *            a String.
 */
public final class UltimatePreferenceItem<T> extends BaseUltimatePreferenceItem {

	private final String mLabel;
	private final T mDefaultValue;
	private final PreferenceType mType;
	private final T[] mChoices;
	private final IUltimatePreferenceItemValidator<T> mPreferenceValidator;
	private final String mToolTip;

	public UltimatePreferenceItem(final String label, final T defaultValue, final PreferenceType type) {
		this(label, defaultValue, type, null, false, null, null);
	}

	public UltimatePreferenceItem(final String label, final T defaultValue, final PreferenceType type,
			final T[] choices, final IUltimatePreferenceItemValidator<T> preferenceValidator) {
		this(label, defaultValue, type, null, false, choices, preferenceValidator);
	}

	public UltimatePreferenceItem(final String label, final T defaultValue, final PreferenceType type,
			final T[] choices) {
		this(label, defaultValue, type, null, false, choices, null);
	}

	public UltimatePreferenceItem(final String label, final T defaultValue, final String desc,
			final PreferenceType type, final T[] choices) {
		this(label, defaultValue, type, desc, false, choices, null);
	}

	public UltimatePreferenceItem(final String label, final T defaultValue, final PreferenceType type,
			final IUltimatePreferenceItemValidator<T> preferenceValidator) {
		this(label, defaultValue, type, null, false, null, preferenceValidator);
	}

	public UltimatePreferenceItem(final String label, final T defaultValue, final String tooltip,
			final PreferenceType type) {
		this(label, defaultValue, type, tooltip, false, null, null);
	}

	public UltimatePreferenceItem(final String label, final T defaultValue, final String tooltip,
			final PreferenceType type, final IUltimatePreferenceItemValidator<T> preferenceValidator) {
		this(label, defaultValue, type, tooltip, false, null, preferenceValidator);
	}

	public UltimatePreferenceItem(final String label, final T defaultValue, final PreferenceType type,
			final String tooltip, final boolean useCustomPreferencePage, final T[] choices,
			final IUltimatePreferenceItemValidator<T> preferenceValidator) {
		mLabel = label;
		mDefaultValue = defaultValue;
		mType = type;
		mChoices = choices;
		mUseCustomPreferencePage = useCustomPreferencePage;
		mPreferenceValidator = preferenceValidator;
		mToolTip = tooltip;

		if (mType == PreferenceType.Radio || mType == PreferenceType.Combo) {
			if (mChoices == null) {
				throw new IllegalArgumentException(
						"You have to supply choices if you use PreferenceType Radio or Combo ");
			}
		}
	}

	public String getLabel() {
		return mLabel;
	}

	public T getDefaultValue() {
		return mDefaultValue;
	}

	@Override
	public PreferenceType getType() {
		return mType;
	}

	public T[] getChoices() {
		return mChoices;
	}

	public String[][] getComboFieldEntries() {
		final String[][] rtr = new String[mChoices.length][2];

		for (int i = 0; i < mChoices.length; ++i) {
			rtr[i][0] = mChoices[i].toString();
			rtr[i][1] = rtr[i][0];
		}
		return rtr;
	}

	public String getToolTip() {
		return mToolTip;
	}

	@Override
	public String toString() {
		return "Pref: " + mLabel + " Type=" + mType + ", Default=" + mDefaultValue;
	}

	public IUltimatePreferenceItemValidator<T> getPreferenceValidator() {
		return mPreferenceValidator;
	}

	@Override
	public List<UltimatePreferenceItem<?>> getFlattenedList() {
		final List<UltimatePreferenceItem<?>> returnList = new ArrayList<>();
		returnList.add(this);
		return returnList;
	}

	public interface IUltimatePreferenceItemValidator<T> {
		/**
		 * An {@link IntegerValidator} that allows all values from 0 to Integer.MAX_VALUE
		 */
		IntegerValidator ONLY_POSITIVE = new IntegerValidator(0, Integer.MAX_VALUE);
		IntegerValidator ONLY_POSITIVE_NON_ZERO = new IntegerValidator(1, Integer.MAX_VALUE);
		IntegerValidator GEQ_TWO = new IntegerValidator(2, Integer.MAX_VALUE);
		StringValidator EXPR_PAIR = new StringValidator("\\s{0,1}((\\w+)\\s*([<>=!][=]*)\\s*(\\w+))\\s{0,1}$");

		boolean isValid(T value);

		String getInvalidValueErrorMessage(T value);

		public class IntegerValidator implements IUltimatePreferenceItemValidator<Integer> {

			private final int mMin;
			private final int mMax;

			public IntegerValidator(final int min, final int max) {
				mMin = min;
				mMax = max;
			}

			@Override
			public boolean isValid(final Integer value) {
				return mMin <= value && value <= mMax;
			}

			@Override
			public String getInvalidValueErrorMessage(final Integer value) {
				return "Valid range is " + mMin + " <= value <= " + mMax;
			}
		}

		public class DoubleValidator implements IUltimatePreferenceItemValidator<Double> {

			private final double mMin;
			private final double mMax;

			public DoubleValidator(final double min, final double max) {
				mMin = min;
				mMax = max;
			}

			@Override
			public boolean isValid(final Double value) {
				return mMin <= value && value <= mMax;
			}

			@Override
			public String getInvalidValueErrorMessage(final Double value) {
				return "Valid range is " + mMin + " <= value <= " + mMax;
			}
		}
		
		public class StringValidator implements IUltimatePreferenceItemValidator<String> {

			private final String mPattern;

			public StringValidator(String pattern) {
				mPattern = pattern;
			}

			@Override
			public boolean isValid(final String string) {
				String[]exprPairs = string.split(",");

				for(String exprPair : exprPairs) {
					Matcher m = match(exprPair, mPattern);
					if(!m.matches()) {
						return false;
					}
				}
				return true;
			}

			@Override
			public String getInvalidValueErrorMessage(final String string) {
				return "Expression pairs " + string + " is not in the format <Variable<Operator>VALUE, ...>";
			}
		}
		
		default Matcher match(String s, String pattern) {
			Pattern p = Pattern.compile(pattern);
	        Matcher m = p.matcher(s);
	        return m;
		}
	}

}
