package local.stalin.plugins.generator.rcfgbuilder.preferences;


import java.io.IOException;

import local.stalin.plugins.generator.rcfgbuilder.Activator;



import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

public class PreferencePage extends FieldEditorPreferencePage implements
		IWorkbenchPreferencePage {
	
	public static final Logger logger =  Logger.getLogger(PreferencePage.class);
	
	private static final ScopedPreferenceStore preferences = 
		new ScopedPreferenceStore(new ConfigurationScope(),Activator.PLUGIN_ID);

	public PreferencePage(){
		super(GRID);
		setPreferenceStore(preferences);
	}

	@Override
	protected void createFieldEditors() {
		
		BooleanFieldEditor multipleStatements = new BooleanFieldEditor(
				PreferenceValues.NAME_MULTIPLE_STATEMENTS,
				PreferenceValues.LABEL_MULTIPLE_STATEMENTS,
				getFieldEditorParent());
		addField(multipleStatements); 
		
		preferences.setDefault(
				PreferenceValues.NAME_MULTIPLE_STATEMENTS, 
				PreferenceValues.DEF_MULTIPLE_STATEMENTS);
	}

	@Override
	public void init(IWorkbench arg0) {
		// TODO Auto-generated method stub

	}
	
	@Override
	public boolean performOk() {
		try{
			preferences.save();
		}catch(IOException ioe){
			logger.warn(ioe);
		}
		return super.performOk();
	}

}
