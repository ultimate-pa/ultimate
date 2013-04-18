/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.blockendcoding.preferences;

import java.io.IOException;
import java.util.ArrayList;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import de.uni_freiburg.informatik.ultimate.blockencoding.rating.RatingFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.blockendcoding.Activator;

/**
 * @author Stefan Wissert
 * 
 */
public class PreferencePage extends FieldEditorPreferencePage implements
		IWorkbenchPreferencePage {

	/**
	 * Logger instance.
	 */
	public static final Logger logger = Logger.getLogger(PreferencePage.class);

	/**
	 * Holds the preference object.
	 */
	private final ScopedPreferenceStore preferences;

	public static final String NAME_CALLMINIMIZE = "MinimizeCall";

	public static final String LABEL_CALLMINIMIZE = "Minimize Call and Return Edges";

	public static final String NAME_EXECUTETESTS = "ExecuteUnitTests";

	public static final String LABEL_EXECUTETESTS = "Execute Unit-Tests, with special Observer";

	public static final String NAME_STRATEGY = "RatingStrategy";

	public static final String LABEL_STRATEGY = "Choose the strategy for the edge rating:";

	public static final String NAME_RATINGBOUND = "RatingBoundary";

	public static final String LABEL_RATINGBOUND = "Enter Rating-Boundary (empty for LBE):";
	
	public static final String NAME_USESTATHEURISTIC = "UseStatisticBasedHeuristic";
	
	public static final String LABEL_USESTATHEURISTIC = "Enable Statistic-Based Heuristic: ";

	public PreferencePage() {
		super(GRID);
		preferences = new ScopedPreferenceStore(ConfigurationScope.INSTANCE,
				Activator.s_PLUGIN_ID);
		setPreferenceStore(preferences);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.jface.preference.FieldEditorPreferencePage#createFieldEditors
	 * ()
	 */
	@Override
	protected void createFieldEditors() {
		BooleanFieldEditor useCallReturnMinimization = new BooleanFieldEditor(
				NAME_CALLMINIMIZE, LABEL_CALLMINIMIZE, getFieldEditorParent());
		addField(useCallReturnMinimization);
		preferences.setDefault(NAME_CALLMINIMIZE, false);

		BooleanFieldEditor executeUnitTests = new BooleanFieldEditor(
				NAME_EXECUTETESTS, LABEL_EXECUTETESTS, getFieldEditorParent());
		addField(executeUnitTests);
		preferences.setDefault(NAME_EXECUTETESTS, false);

		// ComboBox for choosing a rating strategy
		ArrayList<String[]> strategies = new ArrayList<String[]>();
		for (RatingFactory.RatingStrategy strategy : RatingFactory.RatingStrategy
				.values()) {
			String[] entryNamesAndValue = new String[2];
			entryNamesAndValue[0] = strategy.name();
			entryNamesAndValue[1] = Integer.toString(strategy.ordinal());
			strategies.add(entryNamesAndValue);
		}
		ComboFieldEditor ratingStrategy = new ComboFieldEditor(NAME_STRATEGY,
				LABEL_STRATEGY, strategies.toArray(new String[0][]),
				getFieldEditorParent());
		addField(ratingStrategy);
		preferences.setDefault(NAME_STRATEGY, "0");
		// Boolean field, to use the statistic based heuristic
		BooleanFieldEditor useStatisticBasedHeuristic = new BooleanFieldEditor(
				NAME_USESTATHEURISTIC, LABEL_USESTATHEURISTIC, getFieldEditorParent());
		addField(useStatisticBasedHeuristic);
		preferences.setDefault(NAME_USESTATHEURISTIC, false);

		// Text-Field for entering max rating value
		StringFieldEditor ratingBound = new StringFieldEditor(NAME_RATINGBOUND,
				LABEL_RATINGBOUND, getFieldEditorParent());
		addField(ratingBound);
		preferences.setDefault(LABEL_RATINGBOUND, "");
	}

	@Override
	public void init(IWorkbench workbench) {
		// unused
	}

	@Override
	public boolean performOk() {
		try {
			preferences.save();
		} catch (IOException ioe) {
			logger.warn(ioe);
		}
		return super.performOk();
	}

}
