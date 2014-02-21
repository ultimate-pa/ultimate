package de.uni_freiburg.informatik.ultimate.core.preferences;

public class UltimatePreferenceItem<T> {

	public enum PreferenceType {
		Boolean, Directory, String, Label, Combo, Radio, Integer, Path, MultilineString, File
	}

	private String mLabel;
	private T mDefaultValue;
	private PreferenceType mType;
	private T[] mChoices;
	private boolean mUseCustomPreferencePage;
	private IUltimatePreferenceItemValidator<T> mPreferenceValidator;

	public UltimatePreferenceItem(String label, T defaultValue,
			PreferenceType type) {
		this(label, defaultValue, type, false, null, null);
	}

	public UltimatePreferenceItem(String label, T defaultValue,
			PreferenceType type, T[] choices,
			IUltimatePreferenceItemValidator<T> preferenceValidator) {
		this(label, defaultValue, type, false, choices, preferenceValidator);
	}

	public UltimatePreferenceItem(String label, T defaultValue,
			PreferenceType type, T[] choices) {
		this(label, defaultValue, type, false, choices, null);
	}

	public UltimatePreferenceItem(String label, T defaultValue,
			PreferenceType type,
			IUltimatePreferenceItemValidator<T> preferenceValidator) {
		this(label, defaultValue, type, false, null, preferenceValidator);
	}

	public UltimatePreferenceItem(String label, T defaultValue,
			PreferenceType type, boolean useCustomPreferencePage, T[] choices,
			IUltimatePreferenceItemValidator<T> preferenceValidator) {
		mLabel = label;
		mDefaultValue = defaultValue;
		mType = type;
		mChoices = choices;
		mUseCustomPreferencePage = useCustomPreferencePage;
		mPreferenceValidator = preferenceValidator;

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

	public void setLabel(String label) {
		mLabel = label;
	}

	public T getDefaultValue() {
		return mDefaultValue;
	}

	public void setDefaultValue(T defaultValue) {
		mDefaultValue = defaultValue;
	}

	public PreferenceType getType() {
		return mType;
	}

	public void setType(PreferenceType type) {
		mType = type;
	}

	public boolean getUseCustomPreferencePage() {
		return mUseCustomPreferencePage;
	}

	public void setUseCustomPreferencePage(boolean useCustomPreferencePage) {
		mUseCustomPreferencePage = useCustomPreferencePage;
	}

	public T[] getChoices() {
		return mChoices;
	}

	public void setChoices(T[] choices) {
		mChoices = choices;
	}

	public String[][] getComboFieldEntries() {
		String[][] rtr = new String[mChoices.length][2];

		for (int i = 0; i < mChoices.length; ++i) {
			rtr[i][0] = mChoices[i].toString();
			rtr[i][1] = rtr[i][0];
		}
		return rtr;
	}

	public IUltimatePreferenceItemValidator<T> getPreferenceValidator() {
		return mPreferenceValidator;
	}

	public void setPreferenceValidator(
			IUltimatePreferenceItemValidator<T> preferenceValidator) {
		mPreferenceValidator = preferenceValidator;
	}

	public interface IUltimatePreferenceItemValidator<T> {
		public boolean isValid(T value);

		public String getInvalidValueErrorMessage(T value);

		public class IntegerValidator implements
				IUltimatePreferenceItemValidator<Integer> {

			private int mMin;
			private int mMax;

			public IntegerValidator(int min, int max) {
				mMin = min;
				mMax = max;
			}

			@Override
			public boolean isValid(Integer value) {
				return mMin <= value && value <= mMax;
			}

			@Override
			public String getInvalidValueErrorMessage(Integer value) {
				return "Valid range is " + mMin + " <= value <= " + mMax;
			}

		}
	}

}
