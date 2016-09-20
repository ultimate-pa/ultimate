/**
 * Represents a toolchain setting.
 */
package de.uni_freiburg.informatik.ultimate.website;



/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 05.03.2012
 */
public class Setting {
	/**
	 * @author Markus Lindenmann
	 * @author Oleksii Saukh
	 * @author Stefan Wissert
	 * @date 05.03.2012
	 */
	public static enum SettingType {
		/**
		 * A drop down setting (enum like property with predefined values)
		 */
		DROPDOWN,
		/**
		 * An integer setting.
		 */
		INTEGER,
		/**
		 * A string setting.
		 */
		STRING,
		/**
		 * A boolean setting.
		 */
		BOOLEAN
	}

	/**
	 * Whether this setting was already changed by the user or not.
	 */
	private boolean mIsDefaultValue;
	/**
	 * The user set value for this setting.
	 */
	private Value mValue;
	/**
	 * The string describing the setting for Ultimate.
	 */
	private final String mSettingString;
	
	/**
	 * The default value, represented in a string. This will later be parsed in
	 * an appropriate value (e.g. int, bool, etc). <br />
	 * Is only allowed to hold multiple values, if the setting type is
	 * <code>SettingType.DROPDOWN</code> and
	 * <code>isMultiSelectable == true</code>
	 */
	private final String[] defaultValue;
	/**
	 * The type of the setting, describing the domain of the settings value.
	 */
	private final SettingType type;
	/**
	 * This decides, whether multiple values can be selected. This is only
	 * considered, if the setting is of type <code>SettingType.DROPDOWN</code>.
	 */
	private final boolean isMultiSelectable;
	/**
	 * Setting name, represented to the user.
	 */
	private final String settingDescription;
	/**
	 * The possible values of a drop down box. This is only considered, if the
	 * setting is of type <code>SettingType.DROPDOWN</code>.
	 */
	private final String[] values;
	/**
	 * Whether this setting can be changed by a user.
	 */
	private final boolean isUserModifiable;

	/**
	 * Full constructor not represented to the users of this class.
	 * 
	 * @param type
	 *            The type of the setting, describing the domain of the settings
	 *            value.
	 * @param ultimateString
	 *            The string describing the setting for Ultimate, i.e. <toolid>/<settingsname>
	 * @param settingDescription
	 *            Setting name as shown to the user.
	 * @param defaultValue
	 *            The default value, represented in a string. This will later be
	 *            parsed in an appropriate value (e.g. int, bool, etc). <br />
	 *            Is only allowed to hold multiple values, if the setting type
	 *            is <code>SettingType.DROPDOWN</code> and
	 *            <code>isMultiSelectable == true</code>
	 * @param isMultiSelectable
	 *            This decides, whether multiple values can be selected. This is
	 *            only considered, if the setting is of type
	 *            <code>SettingType.DROPDOWN</code>.
	 * @param values
	 *            The possible values of a drop down box. This is only
	 *            considered, if the setting is of type
	 *            <code>SettingType.DROPDOWN</code> and should be null
	 *            otherwise!
	 * @param isUserModifiable
	 *            Whether this setting is modifiable by a user.
	 */
	private Setting(final SettingType type, final String ultimateString,
			final String settingDescription, final String[] defaultValue,
			final boolean isMultiSelectable, final String[] values, final boolean isUserModifiable) {
		checkIdentifier(settingDescription);
		for (final String str : defaultValue) {
			checkIdentifier(str);
		}
		if (type == SettingType.DROPDOWN) {
			// values is null, if type != DROPDOWN!
			for (final String str : values) {
				checkIdentifier(str);
			}
		}
		this.type = type;
		mSettingString = ultimateString;
		this.settingDescription = settingDescription;
		this.defaultValue = defaultValue;
		mValue = new Value();
		this.isMultiSelectable = isMultiSelectable;
		this.values = values;
		setDefaultValue(true);
		this.isUserModifiable = isUserModifiable;
	}

	/**
	 * Constructor for <i>not</i> dropdown settings.
	 * 
	 * @param type
	 *            The type of the setting, describing the domain of the settings
	 *            value.
	 * @param ultimateString
	 *            The string describing the setting for Ultimate.
	 * @param settingDescription
	 *            Setting name, represented to the user.
	 * @param defaultValue
	 *            The default value, represented in a string. This will later be
	 *            parsed in an appropriate value (e.g. int, bool, etc). <br />
	 *            Is only allowed to hold multiple values, if the setting type
	 *            is <code>SettingType.DROPDOWN</code> and
	 *            <code>isMultiSelectable == true</code>
	 * @param isUserModifiable
	 *            Whether this setting is modifiable by a user.
	 */
	public Setting(final String ultimateString, final SettingType type, final String settingDescription, final String defaultValue,
			final boolean isUserModifiable) {
		this(type, ultimateString, settingDescription,
				new String[] { defaultValue }, false, null, isUserModifiable);
		if (type.equals(SettingType.DROPDOWN)) {
			throw new IllegalArgumentException(
					"Dropdown type without values is not possible!");
		}
	}

	/**
	 * Constructor for drop down settings.
	 * 
	 * @param ultimateString
	 *            The string describing the setting for Ultimate.
	 * @param settingDescription
	 *            Setting name, represented to the user.
	 * @param defaultValues
	 *            The default values, represented in a string[]. This will later
	 *            be parsed in an appropriate value (e.g. int, bool, etc). <br />
	 *            Is only allowed to hold multiple values, if the setting type
	 *            is <code>SettingType.DROPDOWN</code> and
	 *            <code>isMultiSelectable == true</code>
	 * @param isMultiSelectable
	 *            This decides, whether multiple values can be selected. This is
	 *            only considered, if the setting is of type
	 *            <code>SettingType.DROPDOWN</code>.
	 * @param values
	 *            The possible values of a drop down box. This is only
	 *            considered, if the setting is of type
	 *            <code>SettingType.DROPDOWN</code>.
	 * @param isUserModifiable
	 *            Whether this setting is modifiable by a user.
	 */
	public Setting(final String ultimateString, final String settingDescription,
			final String[] defaultValues, final boolean isMultiSelectable, final String[] values,
			final boolean isUserModifiable) {
		this(SettingType.DROPDOWN, ultimateString, settingDescription,
				defaultValues, isMultiSelectable, values, isUserModifiable);
		if (!isMultiSelectable && defaultValues.length > 1) {
			throw new IllegalArgumentException(
					"Multiselect is false - there cannot be multiple default values!");
		}
	}

	/**
	 * Setter for the boolean parameter name list.
	 * 
	 * @param id
	 *            the identifier to check
	 */
	private static final void checkIdentifier(final String id) {
		//TODO: Repair checking
		
//		if (id.equals("")) {
//			throw new IllegalArgumentException("identifier: empty name given!");
//		}
		//TODO: why was this here?
//		if (id.length() > 135) {
//			throw new IllegalArgumentException("identifier name too long: "
//					+ id);
//		}
	}

	/**
	 * Getter for the ultimate setting string.
	 * 
	 * @return the settingString
	 */
	public String getSettingString() {
		return mSettingString;
	}

	/**
	 * Getter for the ultimate setting id string used to generate HTML and JS
	 * code.
	 * 
	 * @return the setting identifier generated from the setting string.
	 */
	public String getSettingIdentifier() {
		final String s = mSettingString.replaceAll(
				"[^\\p{L}\\p{N}]", "");
		return s.substring(0, s.length()).toLowerCase();
	}

	/**
	 * Getter for the default value(s)
	 * 
	 * @return the defaultValue
	 */
	public String[] getDefaultValue() {
		return defaultValue;
	}

	/**
	 * Getter for the settings type.
	 * 
	 * @return the type
	 */
	public SettingType getType() {
		return type;
	}

	/**
	 * Getter for the boolean whether multiple values in the drop down can be
	 * selected.
	 * 
	 * @return the isMultiSelectable
	 */
	public boolean isMultiSelectable() {
		return isMultiSelectable;
	}

	/**
	 * Whether this setting is user modifiable.
	 * 
	 * @return Whether this setting is modifiable by a user.
	 */
	public boolean isUserModifiable() {
		return isUserModifiable;
	}

	/**
	 * Getter for the setting description represented to the user.
	 * 
	 * @return the settingDescription
	 */
	public String getSettingDescription() {
		return settingDescription;
	}

	/**
	 * Getter for drop down values.
	 * 
	 * @return the values
	 */
	public String[] getValues() {
		return values;
	}

	/**
	 * Setter for the user defined setting.
	 * 
	 * @param value
	 *            the String value holding an int.
	 */
	public void setIntValue(final String value) {
		if (!isUserModifiable) {
			throw new RuntimeException("Setting this value is not allowed!");
		}
		if (type != SettingType.INTEGER) {
			throw new RuntimeException(
					"Mehtod Access not allowd if type != int! type: "
							+ type.toString());
		}
		final int i = Integer.parseInt(value);
		mValue = new Value(null, i, false);
	}

	/**
	 * Setter for user defined setting.
	 * 
	 * @param value
	 *            the String value holding a String.
	 */
	public void setStringValue(final String value) {
		if (!isUserModifiable) {
			throw new RuntimeException("Setting this value is not allowed!");
		}
		if (type != SettingType.STRING) {
			throw new RuntimeException(
					"Mehtod Access not allowd if type != string! type: "
							+ type.toString());
		}
		if (value == null || value.equals("")) {
			throw new IllegalArgumentException("Empty value not allowed");
		}
		boolean isASCII = true;
		for (final char c : value.toCharArray()) {
			if (c < 32 || c >= 127) {
				isASCII = false;
				break;
			}
		}
		if (!isASCII) {
			throw new IllegalArgumentException("String is not in ASCII");
		}
		mValue = new Value(new String[] { value }, 0, false);
	}

	/**
	 * Setter for user defined setting.
	 * 
	 * @param values
	 *            the String value holding the enum values.
	 */
	public void setDropDownValue(final String[] values) {
		if (!isUserModifiable) {
			throw new RuntimeException("Setting this value is not allowed!");
		}
		if (type != SettingType.DROPDOWN) {
			throw new RuntimeException(
					"Mehtod Access not allowd if type != drop down! type: "
							+ type.toString());
		}
		if (values == null || values.length == 0) {
			throw new IllegalArgumentException("Empty value list not allowed");
		}
		if (!isMultiSelectable && values.length != 1) {
			throw new IllegalArgumentException("Only one selection allowed!");
		}
		VALS: for (final String s : values) {
			for (final String c : this.values) {
				if (s.equals(c)) {
					continue VALS;
				}
			}
			// not contained in predefined domain (dropdown values)!
			// this will also handle empty strings, because this.values cannot
			// contain an empty string!
			throw new IllegalArgumentException("Not a valid enum value!");
		}
		mValue = new Value(values, 0, false);
	}

	/**
	 * Setter for user defined setting.
	 * 
	 * @param value
	 *            the String value holding a Boolean.
	 */
	public void setBooleanValue(final String value) {
		if (!isUserModifiable) {
			throw new RuntimeException("Setting this value is not allowed!");
		}
		if (type != SettingType.BOOLEAN) {
			throw new RuntimeException(
					"Mehtod Access not allowd if type != boolean! type: "
							+ type.toString());
		}
		final boolean b = Boolean.parseBoolean(value);
		mValue = new Value(null, 0, b);
	}

	/**
	 * Getter for the set values for this setting.
	 * 
	 * @return the set values.
	 */
	public String getSetValues() {
		return mValue.toString();
	}

	/**
	 * Whether the value of this setting was changed.
	 * @return whether the value of this setting was changed.
	 */
	boolean isDefaultValue() {
		return mIsDefaultValue;
	}

	/**
	 * Change whether the value of this setting was changed.
	 * @param isDefaultValue set whether the value of this setting was changed.
	 */
	void setDefaultValue(final boolean isDefaultValue) {
		mIsDefaultValue = isDefaultValue;
	}

	/**
	 * @author Markus Lindenmann
	 * @author Oleksii Saukh
	 * @author Stefan Wissert
	 * @date 07.03.2012
	 */
	private class Value {
		/**
		 * 
		 */
		private String valueString;
		/**
		 * 
		 */
		private int valueInt;
		/**
		 * 
		 */
		private boolean valueBoolean;
		/**
		 * 
		 */
		private String[] valueDropdown;

		/**
		 * Constructor.
		 * 
		 * Expects that only the required field is set (i.e. valString=null,
		 * valInt=0, valBool=false if not applicable).
		 * 
		 * @param valStr
		 *            String[]
		 * @param valInt
		 *            int
		 * @param valBool
		 *            boolean
		 */
		protected Value(final String[] valStr, final int valInt, final boolean valBool) {
			switch (getType()) {
			case BOOLEAN:
				if (valStr != null || valInt != 0) {
					throw new IllegalArgumentException(
							"Only boolean value expected!");
				}
				valueBoolean = valBool;
				break;
			case DROPDOWN:
				if (valInt != 0 || valBool) {
					throw new IllegalArgumentException(
							"Only String value expected!");
				}
				if (valStr == null
						|| (!isMultiSelectable() && valStr.length != 1)) {
					throw new IllegalArgumentException(
							"String[] of length 1 is expected");
				}
				if (valStr.length == 0) {
					throw new IllegalArgumentException(
							"String[] of length >0 is expected");
				}
				for (final String s : valStr) {
					if (s == null || s.equals("")) {
						throw new IllegalArgumentException(
								"Strings expected to hold a value!");
					}
				}
				valueDropdown = valStr;
				break;
			case INTEGER:
				if (valStr != null || valBool) {
					throw new IllegalArgumentException(
							"Only int value expected!");
				}
				valueInt = valInt;
				break;
			case STRING:
				if (valInt != 0 || valBool) {
					throw new IllegalArgumentException(
							"Only String value expected!");
				}
				if (valStr == null || valStr.length != 1) {
					throw new IllegalArgumentException(
							"String[] of length 1 is expected");
				}
				if (valStr[0] == null || valStr[0].equals("")) {
					throw new IllegalArgumentException(
							"String[0] expected to hold a value!");
				}
				valueString = valStr[0];
				break;
			default:
				throw new UnsupportedOperationException(
						"The given type is unknown!");

			}
			setDefaultValue(false);
		}

		/**
		 * The initially set value - this represents a default value and should
		 * only be used within the full constructor of the Setting class!
		 */
		Value() {
			// represents a default value and cannot do anything else but return
			// the default value string in the toString() method!
		}

		/**
		 * @return returns a string representation of this value. In case of
		 *         multi-selectable drop down box, a comma separated value list
		 *         is returned.
		 */
		@Override
		public final String toString() {
			if (isDefaultValue()) {
				if (getType() == SettingType.DROPDOWN) {
					final StringBuffer sb = new StringBuffer();
					for (final String s : getDefaultValue()) {
						sb.append(s).append(",");
					}
					sb.deleteCharAt(sb.length() - 1);
					return sb.toString();
				}
				return getDefaultValue()[0];
			}
			switch (getType()) {
			case BOOLEAN:
				return Boolean.toString(valueBoolean);
			case DROPDOWN:
				if (isMultiSelectable()) {
					final StringBuffer sb = new StringBuffer();
					for (final String s : valueDropdown) {
						sb.append(s).append(",");
					}
					sb.deleteCharAt(sb.length() - 1);
					return sb.toString();
				}
				return valueDropdown[0];
			case INTEGER:
				return Integer.toString(valueInt);
			case STRING:
				return valueString;
			default:
				throw new UnsupportedOperationException("The given type is unknown!");
			}
		}
	}
}
