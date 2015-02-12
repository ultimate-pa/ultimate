package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.preferences;

import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.Activator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;

/**
 * All items from the plug-in's preferences.
 * The current set preferences can be queried on each item.
 * Each item contains the label name, default value and list choices (if available).
 * The preferences dialog should show the items in the order of this enum.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public enum PreferenceItem {

	LABEL___ENABLE_INLINING_FOR("Enable inlining for ..."),
	INLINE_UNIMPLEMENTED("calls to unimplemented procedures", true, PreferenceType.Boolean),
	INLINE_IMPLEMENTED("calls to implemented procedures", true, PreferenceType.Boolean),
	INLINE_CALL_FORALL("call-forall statements", true, PreferenceType.Boolean),
	
	LABEL___IGNORE_CALLS("\nIgnore calls to ..."),
	IGNORE_POLYMORPHIC("and inside polymorphic procedures *", true, PreferenceType.Boolean),
	IGNORE_RECURSIVE("recursive procedures *", true, PreferenceType.Boolean),
	IGNORE_MULTIPLE_CALLED("procedures, called more than once", false, PreferenceType.Boolean),
	NOTE___CANCEL_TOOLCHAIN("* = or else the toolchain will be canceled"),

	LABEL___USER_LIST("\nUser list (procedure ids, separated by whitespace)"),
	USER_LIST("User list", "", PreferenceType.MultilineString),
	USER_LIST_TYPE("user list type", UserListType.BLACKLIST_RESTRICT, PreferenceType.Combo, UserListType.values()),

	LABEL___SPECIFICATION_INLINING("\nSpecification inlining"),
	ASSUME_PRE_AFTER_ASSERT("Assume inlined preconditions after assertion", true, PreferenceType.Boolean);

	protected final String mName;
	protected final Object mDefaultValue;
	protected final PreferenceType mType;
	protected final Object[] mChoices;
	
	private PreferenceItem(String name) {
		this(name, null, PreferenceType.Label, null);
	}
	
	private PreferenceItem(String name, Object defaultValue, PreferenceType type) {
		this(name, defaultValue, type, null);
	}
	
	private PreferenceItem(String name, Object defaultValue, PreferenceType type, Object[] choices) {
		mName = name;
		mDefaultValue = defaultValue;
		mType = type;
		mChoices = choices;
	}
	
	public String getName() {
		return mName;
	}
	
	public PreferenceType getType() {
		return mType;
	}
	
	public Object getDefaultValue() {
		return mDefaultValue;
	}
	
	public Boolean getBooleanValue() {
		return new UltimatePreferenceStore(Activator.PLUGIN_ID).getBoolean(mName);
	}
	
	public String getStringValue() {
		return new UltimatePreferenceStore(Activator.PLUGIN_ID).getString(mName);
	}
	
	public UserListType getUserListTypeValue() {
		return new UltimatePreferenceStore(Activator.PLUGIN_ID).getEnum(mName, UserListType.class);
	}

	public UltimatePreferenceItem<?> newUltimatePreferenceItem() {
		return new UltimatePreferenceItem<Object>(mName, mDefaultValue, mType, mChoices);
	}
}
