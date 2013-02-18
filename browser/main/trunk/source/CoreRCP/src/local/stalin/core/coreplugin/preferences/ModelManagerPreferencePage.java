package local.stalin.core.coreplugin.preferences;


import local.stalin.core.coreplugin.Activator;

import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.DirectoryFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.MessageBox;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

/**
 * ModelManagerPreferencePage that allows us to set 1) the temporary
 * directory where Stalin stores its models, 2) whether want the 
 * temporary directory to be cleaned up at the exit of Stalin.
 * 
 * @author Christian Simon
 * 
 */
public class ModelManagerPreferencePage extends FieldEditorPreferencePage
implements IWorkbenchPreferencePage {

	private static IPreferenceStore prefStore = new ScopedPreferenceStore(
			new InstanceScope(), Activator.s_PLUGIN_ID);

	boolean tmp_dir_change = false;
	
	
	@Override
	protected void createFieldEditors() {
		
		BooleanFieldEditor dropModels = new BooleanFieldEditor(IPreferenceConstants.PREFID_MM_DROP_MODELS,
															   IPreferenceConstants.LABEL_MM_DROPMODELS,
															   getFieldEditorParent());
		
		
		DirectoryFieldEditor tmpDir = new DirectoryFieldEditor(IPreferenceConstants.PREFID_MM_TMPDIRECTORY,
															   IPreferenceConstants.LABEL_MM_TMPDIRECTORY,
															   getFieldEditorParent());
		addField(dropModels);
		addField(tmpDir);
		
	}

	
	
	@Override
	public void propertyChange(org.eclipse.jface.util.PropertyChangeEvent event) {
		if (event.getSource() instanceof DirectoryFieldEditor) {
			tmp_dir_change = true;
		}
		super.propertyChange(event);
	}



	@Override
	public void init(IWorkbench workbench) {
		// set the defaults
		prefStore.setDefault(IPreferenceConstants.PREFID_MM_DROP_MODELS, IPreferenceConstants.DEFAULT_MM_DROP_MODELS);
		setPreferenceStore(prefStore);

	}

	@Override
	public boolean performOk() {
		if (tmp_dir_change) {
			MessageBox box = new MessageBox(getFieldEditorParent().getShell(), SWT.OK | SWT.ICON_INFORMATION);
			box.setMessage("Please note that Stalin needs to be restarted for changes to the temporary directory to become effective.");
			box.open();
		}
		return super.performOk();
	}
	
	

}
