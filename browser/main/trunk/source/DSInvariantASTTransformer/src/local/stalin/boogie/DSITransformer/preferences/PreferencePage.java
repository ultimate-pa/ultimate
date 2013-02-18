package local.stalin.boogie.DSITransformer.preferences;

import java.io.IOException;

import local.stalin.boogie.DSITransformer.Activator;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

/**
 * the preference page for the< Data Structure Invariant Transformer
 * 
 * this calls contributes to the extension point: org.eclipse.ui.preferencePages
 * see at the plugin.xml
 * 
 * @author arenis
 */

public class PreferencePage extends FieldEditorPreferencePage implements
		IWorkbenchPreferencePage {

	public static final Logger logger = Logger.getLogger(PreferencePage.class);

	private final ScopedPreferenceStore preferences;

	public PreferencePage() {
		super(GRID);
		preferences = new ScopedPreferenceStore(new ConfigurationScope(),
				Activator.s_PLUGIN_ID);
		setPreferenceStore(preferences);

	}

	// @Override
	protected void createFieldEditors() {

		// Procedure Name
		addField(new StringFieldEditor(PreferenceValues.NAME_PROCEDUREID,
				PreferenceValues.LABEL_PROCEDUREID, getFieldEditorParent()));

		// Consider all functions
		BooleanFieldEditor allFunctions = new BooleanFieldEditor(
				PreferenceValues.NAME_ALLFUNCTIONS,
				PreferenceValues.LABEL_ALLFUNCTIONS,
				BooleanFieldEditor.SEPARATE_LABEL, getFieldEditorParent());

		// Connect the fields
		allFunctions.setPropertyChangeListener(new IPropertyChangeListener() {

			@Override
			public void propertyChange(
					org.eclipse.jface.util.PropertyChangeEvent event) {
				Object x = event.getNewValue();
				logger.debug(x);
			}
		});
		addField(allFunctions);

		// Structure Type
		StringFieldEditor structureType = new StringFieldEditor(
				PreferenceValues.NAME_STRUCTURETYPE,
				PreferenceValues.LABEL_STRUCTURETYPE, getFieldEditorParent());
		addField(structureType);

		// Trim After Wrap
		BooleanFieldEditor trimAfterWrap = new BooleanFieldEditor(
				PreferenceValues.NAME_TRIMWRAP,
				PreferenceValues.LABEL_TRIMWRAP,
				BooleanFieldEditor.SEPARATE_LABEL, getFieldEditorParent());
		addField(trimAfterWrap);
		
		// Leave all procedures
		BooleanFieldEditor leaveOriginalProcedures = new BooleanFieldEditor(
				PreferenceValues.NAME_LEAVEPROCEDURES,
				PreferenceValues.LABEL_LEAVEPROCEDURES,
				BooleanFieldEditor.SEPARATE_LABEL, getFieldEditorParent());
		addField(leaveOriginalProcedures);
	}

	public void init(IWorkbench workbench) {
	}

	public boolean performOk() {
		try {
			preferences.save();
		} catch (IOException ioe) {
			logger.warn(ioe);
		}
		return super.performOk();
	}

}
