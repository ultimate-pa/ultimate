package local.stalin.core.coreplugin.preferences;

import java.io.IOException;

import local.stalin.core.api.StalinServices;
import local.stalin.core.coreplugin.Activator;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

/**
 * the preference page for the 2dgraph plugin
 * should also serve as template for other pluginspref-pages
 * 
 * this calls contributes to the extensionpoint:
 * org.eclipse.ui.prefgerencePages   see at the plugin.xml
 * 
 * @author Christian Ortolf
 */
public class CorePreferencePage extends FieldEditorPreferencePage
		implements IWorkbenchPreferencePage {

	static{
		s_Logger = StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	}
	
	private static final Logger s_Logger;
	private ScopedPreferenceStore m_Preference;

	public CorePreferencePage(){
		super(GRID);
		m_Preference = new ScopedPreferenceStore(new ConfigurationScope(),Activator.s_PLUGIN_ID);
		setPreferenceStore(m_Preference);

		
	}
	//@Override
	protected void createFieldEditors() {
		//a Field editor for files... there are several other FieldEditors availabel
		BooleanFieldEditor showusableparser = new BooleanFieldEditor(IPreferenceConstants.s_NAME_SHOWUSABLEPARSER,
				IPreferenceConstants.s_LABEL_SHOWUSABLEPARSER,getFieldEditorParent());

		addField(showusableparser); 
	}

	public void init(IWorkbench workbench) {}

	
	public boolean performOk() {
		try{
			m_Preference.save();
		}catch(IOException ioe){
			s_Logger.warn(ioe);
		}
		return super.performOk();
	}
	
}
