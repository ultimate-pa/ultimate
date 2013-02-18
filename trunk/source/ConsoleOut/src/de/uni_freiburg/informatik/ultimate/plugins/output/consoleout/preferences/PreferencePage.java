package de.uni_freiburg.informatik.ultimate.plugins.output.consoleout.preferences;

import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.plugins.output.consoleout.Activator;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

/**
 * the preference page for the consoleout plugin
 * 
 * this calls contributes to the extensionpoint:
 * org.eclipse.ui.prefgerencePages   see at the plugin.xml
 * 
 * @author dietsch
 */
public class PreferencePage extends FieldEditorPreferencePage
		implements IWorkbenchPreferencePage {

	public static final Logger logger =  Logger.getLogger(PreferencePage.class);
	
	
	private final ScopedPreferenceStore preferences;

	public PreferencePage(){
		super(GRID);
		preferences = new ScopedPreferenceStore(new ConfigurationScope(),Activator.s_PLUGIN_ID);
		setPreferenceStore(preferences);

		
	}
	//@Override
	protected void createFieldEditors() {

		BooleanFieldEditor showAllAnnotations = new BooleanFieldEditor(PreferenceValues.NAME_SHOWALLANNOTATIONS,
				PreferenceValues.LABEL_SHOWALLANNOTATIONS,getFieldEditorParent());
		
		addField(showAllAnnotations); 
	}

	public void init(IWorkbench workbench) {}

	
	public boolean performOk() {
		try{
			preferences.save();
		}catch(IOException ioe){
			logger.warn(ioe);
		}
		return super.performOk();
	}
	
}
