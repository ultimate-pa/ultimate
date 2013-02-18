package local.stalin.plugins.safetychecker.preferences;

import java.io.IOException;

import local.stalin.plugins.safetychecker.Activator;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.DirectoryFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

/**
 * the preference page for the safety checker
 * 
 * this calls contributes to the extensionpoint:
 * org.eclipse.ui.prefgerencePages   see at the plugin.xml
 * 
 * @author ermis
 */
public class PreferencePage extends FieldEditorPreferencePage
		implements IWorkbenchPreferencePage {

	public static final Logger logger =  Logger.getLogger(PreferencePage.class);
	
	
	private final ScopedPreferenceStore preferences;

	public PreferencePage(){
		super(GRID);
		preferences = new ScopedPreferenceStore(new ConfigurationScope(),Activator.PLUGIN_ID);
		setPreferenceStore(preferences);

		
	}
	//@Override
	protected void createFieldEditors() {

		BooleanFieldEditor activateDumpFile = new BooleanFieldEditor(PreferenceValues.NAME_ACTIVATEDUMPFORMULA,
				PreferenceValues.LABEL_ACTIVATEDUMPFORMULA,getFieldEditorParent());
		
		addField(activateDumpFile); 
		
		DirectoryFieldEditor dumpPath = new DirectoryFieldEditor(PreferenceValues.NAME_DUMPPATH, PreferenceValues.LABEL_DUMPPATH,
				getFieldEditorParent());
		
		addField(dumpPath);
		
		IntegerFieldEditor maxStepNumber = new IntegerFieldEditor(PreferenceValues.NAME_MAXSTEPNUMBER, PreferenceValues.LABEL_MAXSTEPNUMBER,
				getFieldEditorParent(), 3);
		maxStepNumber.setValidRange(0, PreferenceValues.VALUE_MAXSTEPNUMBER_MAX);
		addField(maxStepNumber);
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
