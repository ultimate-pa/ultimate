package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.preferences;

import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.Activator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;

/**
 * All items from the plug-in's preferences.
 * The current set preferences can be queried on each item.
 * Each item contains the label name, default value and list choices (if available).
 * The preferences dialog should show these items in the same order as in this enum.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public enum PreferenceItem {

	LABEL___ENABLE_INLINING_FOR("Enable inlining for"),
	INLINE_UNIMPLEMENTED("calls of unimplemented procedures", true, PreferenceType.Boolean),
	INLINE_IMPLEMENTED("calls of implemented procedures", true, PreferenceType.Boolean),
	INLINE_SINGLE_CALLS_ONLY("single calls only", true, PreferenceType.Boolean),
	INLINE_FREE_CALLS("call-forall statements", true, PreferenceType.Boolean),
	
	LABEL___USER_LIST("\nUser list (procedure ids, separated by whitespace)"),
	USER_LIST("User list", "", PreferenceType.MultilineString),
	USER_LIST_TYPE("user list type", UserListType.BLACKLIST_RESTRICT,
			PreferenceType.Combo, UserListType.values()),

	LABEL___BEHAVIOR_ON_RECURSION("\nBehavior on attempts to inline calls to (possibly) recursive procedures"),
	BEHAVIOR_ON_EXTERN_RECUSRIVE_CALL("Extern calls", BehaviorOnRecursion.SKIP,
			PreferenceType.Combo, BehaviorOnRecursion.values()),
	BEHAVIOR_ON_INTERN_RECUSRIVE_CALL("Intern calls", BehaviorOnRecursion.WARN_AND_SKIP,
			PreferenceType.Combo, BehaviorOnRecursion.values()),
	
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
	
	public BehaviorOnRecursion getBehaviorOnRecursionValue() {
		return new UltimatePreferenceStore(Activator.PLUGIN_ID).getEnum(mName, BehaviorOnRecursion.class);
	}
	
	public UltimatePreferenceItem<?> newUltimatePreferenceItem() {
		return new UltimatePreferenceItem<Object>(mName, mDefaultValue, mType, mChoices);
	}
}
