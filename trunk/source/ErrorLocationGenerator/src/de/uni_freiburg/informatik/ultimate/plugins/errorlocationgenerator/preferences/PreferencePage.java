package de.uni_freiburg.informatik.ultimate.plugins.errorlocationgenerator.preferences;

import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.plugins.errorlocationgenerator.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.errorlocationgenerator.preferences.PreferenceValues;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

public class PreferencePage extends FieldEditorPreferencePage
implements IWorkbenchPreferencePage {


	public static final Logger logger =  Logger.getLogger(PreferencePage.class);
	
	
	private final ScopedPreferenceStore preferences;

	public PreferencePage(){
		super(GRID);
		preferences = new ScopedPreferenceStore(ConfigurationScope.INSTANCE,Activator.PLUGIN_ID);
		setPreferenceStore(preferences);
	}
	
	@Override
	protected void createFieldEditors() {
		BooleanFieldEditor checkValidity = new BooleanFieldEditor(PreferenceValues.NAME_CHECKVALIDITYOFERROREDGE,
				PreferenceValues.LABEL_CHECKVALIDITYOFERROREDGE,getFieldEditorParent());
		addField(checkValidity);
		BooleanFieldEditor checkDeadcode = new BooleanFieldEditor(PreferenceValues.NAME_CHECKFORDEADCODE,
				PreferenceValues.LABEL_CHECKFORDEADCODE,getFieldEditorParent());
		addField(checkDeadcode); 
		BooleanFieldEditor checkReachability = new BooleanFieldEditor(PreferenceValues.NAME_CHECKREACHABILITY,
				PreferenceValues.LABEL_CHECKREACHABILITY,getFieldEditorParent());
		addField(checkReachability); 
	}

	@Override
	public void init(IWorkbench workbench) {
		// TODO Auto-generated method stub
		
	}
	
	public boolean performOk() {
		try{
			preferences.save();
		}catch(IOException ioe){
			logger.warn(ioe);
		}
		return super.performOk();
	}
}
