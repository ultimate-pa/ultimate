/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.blockendcoding.preferences;

import java.io.IOException;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

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

	public static String NAME_CALLMINIMIZE = "MinimizeCall";

	public static String LABEL_CALLMINIMIZE = "Minimize Call and Return Edges";
	
	public static String NAME_EXECUTETESTS = "ExecuteUnitTests";
	
	public static String LABEL_EXECUTETESTS = "Excute Unit-Tests, with special Observer";

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
