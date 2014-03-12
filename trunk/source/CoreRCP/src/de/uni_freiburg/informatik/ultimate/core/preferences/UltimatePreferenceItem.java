package de.uni_freiburg.informatik.ultimate.core.preferences;

/**
 * An UltimatePReferenceItem describes exactly one setting of a preference.
 * Based on its {@link PreferenceType}, the active {@link IController} will
 * present it to users for modification.
 * 
 * @author dietsch
 * 
 * @param <T>
 *            The type of the preference. Usually a primitive, an enum, or
 *            something that can be easily constructed from a String.
 */
public class UltimatePreferenceItem<T> {

	/**
	 * PreferenceType describes, how a preference item should be presented to
	 * the user by the active {@link IController}.
	 * 
	 * @author dietsch
	 * 
	 */
	public enum PreferenceType {
		/**
		 * Yes/no choice. Usually a single check-box or a flag.
		 */
		Boolean,
		/**
		 * A string representing an absolute path to a single directory on the
		 * local file system.
		 */
		Directory,
		/**
		 * A single line of text.
		 */
		String,
		/**
		 * A non-editable label that can be used to describe parts of the
		 * preferences.
		 * 
		 * @see {@link UltimatePreferenceInitializer#initializeDefaultPreferences()}
		 *      for more information on positioning
		 *      {@link UltimatePreferenceItem UltimatePreferenceItems}.
		 */
		Label,
		/**
		 * Presents the user with a single choice from some predefined values.
		 * Can be used for e.g. Enums.
		 * 
		 * Differs from {@link #Radio} because the guideline is that Combo does
		 * not show all values simultaneously (think Combobox,
		 * Radiobuttons/Radiolist).
		 */
		Combo,
		/**
		 * Presents the user with a single choice from some predefined values.
		 * Can be used for e.g. Enums.
		 * 
		 * Differs from {@link #Combo} because the guideline is that Radio shows
		 * all values simultaneously.
		 */
		Radio,
		/**
		 * A single number representing an Integer.
		 */
		Integer,
		/**
		 * A string representing one or multiple paths to a file or directory on
		 * the system. If multiple paths are specified by the user, they are
		 * separated by a semicolon.
		 */
		Path,
		/**
		 * A string spanning multiple lines. The lines are separated by the
		 * system-default line break character (e.g. \r or \n).
		 */
		MultilineString,
		/**
		 * A string representing an absolute path on the local file system to a
		 * single file.
		 */
		File,
		/**
		 * A string representing a color. The string has to be of the form
		 * "red,green,blue", where 0 <= red,green,blue <= 255.
		 */
		Color
	}

	private String mLabel;
	private T mDefaultValue;
	private PreferenceType mType;
	private T[] mChoices;
	private boolean mUseCustomPreferencePage;
	private IUltimatePreferenceItemValidator<T> mPreferenceValidator;

	public UltimatePreferenceItem(String label, T defaultValue, PreferenceType type) {
		this(label, defaultValue, type, false, null, null);
	}

	public UltimatePreferenceItem(String label, T defaultValue, PreferenceType type, T[] choices,
			IUltimatePreferenceItemValidator<T> preferenceValidator) {
		this(label, defaultValue, type, false, choices, preferenceValidator);
	}

	public UltimatePreferenceItem(String label, T defaultValue, PreferenceType type, T[] choices) {
		this(label, defaultValue, type, false, choices, null);
	}

	public UltimatePreferenceItem(String label, T defaultValue, PreferenceType type,
			IUltimatePreferenceItemValidator<T> preferenceValidator) {
		this(label, defaultValue, type, false, null, preferenceValidator);
	}

	public UltimatePreferenceItem(String label, T defaultValue, PreferenceType type, boolean useCustomPreferencePage,
			T[] choices, IUltimatePreferenceItemValidator<T> preferenceValidator) {
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

	public void setPreferenceValidator(IUltimatePreferenceItemValidator<T> preferenceValidator) {
		mPreferenceValidator = preferenceValidator;
	}

	public interface IUltimatePreferenceItemValidator<T> {
		public boolean isValid(T value);

		public String getInvalidValueErrorMessage(T value);

		public class IntegerValidator implements IUltimatePreferenceItemValidator<Integer> {

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
