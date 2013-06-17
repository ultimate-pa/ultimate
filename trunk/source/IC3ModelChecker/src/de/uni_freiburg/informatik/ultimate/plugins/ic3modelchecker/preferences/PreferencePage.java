package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.preferences;

import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.Activator;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
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
