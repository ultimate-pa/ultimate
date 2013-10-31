package de.uni_freiburg.informatik.ultimate.core.preferences;

public class UltimatePreferenceItem {

	public enum PreferenceType {
		Boolean, Directory, String, Label
	}

	private String mLabel;
	private Object mDefaultValue;
	private PreferenceType mType;
	private Object[] mChoices;
	private boolean mUseCustomPreferencePage;

	public UltimatePreferenceItem(String label, Object defaultValue,
			PreferenceType type, Object[] choices) {
		this(label, defaultValue, type, false, choices);
	}

	public UltimatePreferenceItem(String label, Object defaultValue,
			PreferenceType type, boolean useCustomPreferencePage,
			Object[] choices) {
		mLabel = label;
		mDefaultValue = defaultValue;
		mType = type;
		mChoices = choices;
		mUseCustomPreferencePage = useCustomPreferencePage;
	}

	public String getLabel() {
		return mLabel;
	}

	public void setLabel(String label) {
		mLabel = label;
	}

	public Object getDefaultValue() {
		return mDefaultValue;
	}

	public void setDefaultValue(Object defaultValue) {
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

	public Object[] getChoices() {
		return mChoices;
	}

	public void setChoices(Object[] choices) {
		mChoices = choices;
	}

}
