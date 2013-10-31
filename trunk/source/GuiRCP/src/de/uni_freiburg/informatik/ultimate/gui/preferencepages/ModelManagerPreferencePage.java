package de.uni_freiburg.informatik.ultimate.gui.preferencepages;


import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;

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
 * directory where Ultimate stores its models, 2) whether want the 
 * temporary directory to be cleaned up at the exit of Ultimate.
 * 
 * @author Christian Simon
 * 
 */
public class ModelManagerPreferencePage extends FieldEditorPreferencePage
implements IWorkbenchPreferencePage {

	private static IPreferenceStore prefStore = new ScopedPreferenceStore(
			InstanceScope.INSTANCE , Activator.s_PLUGIN_ID);

	boolean tmp_dir_change = false;
	
	
	@Override
	protected void createFieldEditors() {
		
		BooleanFieldEditor dropModels = new BooleanFieldEditor(CorePreferenceInitializer.LABEL_MM_DROP_MODELS,
															   CorePreferenceInitializer.LABEL_MM_DROP_MODELS,
															   getFieldEditorParent());
		
		
		DirectoryFieldEditor tmpDir = new DirectoryFieldEditor(CorePreferenceInitializer.LABEL_MM_TMPDIRECTORY,
															   CorePreferenceInitializer.LABEL_MM_TMPDIRECTORY,
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
		setPreferenceStore(prefStore);

	}

	@Override
	public boolean performOk() {
		if (tmp_dir_change) {
			MessageBox box = new MessageBox(getFieldEditorParent().getShell(), SWT.OK | SWT.ICON_INFORMATION);
			box.setMessage("Please note that Ultimate needs to be restarted for changes to the temporary directory to become effective.");
			box.open();
		}
		return super.performOk();
	}
	
	

}
