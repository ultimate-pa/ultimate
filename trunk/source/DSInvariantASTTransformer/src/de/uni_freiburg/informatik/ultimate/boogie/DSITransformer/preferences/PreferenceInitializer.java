package de.uni_freiburg.informatik.ultimate.boogie.DSITransformer.preferences;

import de.uni_freiburg.informatik.ultimate.boogie.DSITransformer.Activator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;

/**
 * 
 * This class loads preference default values before they are needed
 * 
 * contributes to ep: org.eclipse.core.runtime.preferences.initializer see the
 * plugin.xml
 * 
 * @author Dietsch
 * 
 */
public class PreferenceInitializer extends UltimatePreferenceInitializer {

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<String>(LABEL_PROCEDUREID, "",
						PreferenceType.String),
				new UltimatePreferenceItem<Boolean>(LABEL_ALLFUNCTIONS,
						VALUE_ALLFUNCTIONS_DEFAULT, PreferenceType.Boolean),
				new UltimatePreferenceItem<String>(LABEL_STRUCTURETYPE, "",
						PreferenceType.String),
				new UltimatePreferenceItem<Boolean>(LABEL_TRIMWRAP,
						VALUE_TRIMWRAP_DEFAULT, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_LEAVEPROCEDURES,
						VALUE_LEAVEPROCEDURES, PreferenceType.Boolean), };
	}

	@Override
	protected String getPlugID() {
		return Activator.s_PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return "DS Invariant AST Transformer";
	}

	/*
	 * labels for the different preferences
	 */

	public static String LABEL_STRUCTURETYPE = "Structure Type";
	public static String LABEL_PROCEDUREID = "New Procedure Identifier";
	public static String LABEL_TRIMWRAP = "Trim after \"$wrap\"?";
	public static String LABEL_ALLFUNCTIONS = "All methods (ignores all other options)";
	public static String LABEL_LEAVEPROCEDURES = "Don't remove original procedure declarations?";

	/*
	 * default values for the different preferences
	 */

	public static boolean VALUE_TRIMWRAP_DEFAULT = true;
	public static boolean VALUE_ALLFUNCTIONS_DEFAULT = false;
	public static boolean VALUE_LEAVEPROCEDURES = false;

}
