package de.uni_freiburg.informatik.ultimate.gui.preferencepages;

import java.io.IOException;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.DirectoryFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;

public class UltimateGeneratedPreferencePage extends FieldEditorPreferencePage
		implements IWorkbenchPreferencePage {

	private String mPluginID;
	private UltimatePreferenceItem[] mDefaultPreferences;
	private String mTitle;
	private ScopedPreferenceStore mPreferenceStore;

	public UltimateGeneratedPreferencePage(String pluginID, String title,
			UltimatePreferenceItem[] preferences) {
		super(GRID);
		mPluginID = pluginID;
		mDefaultPreferences = preferences;
		mTitle = title;
		mPreferenceStore = new ScopedPreferenceStore(new UltimatePreferenceStore(mPluginID).getScopeContext(),
				mPluginID);
		setPreferenceStore(mPreferenceStore);
		setTitle(mTitle);
	}

	public UltimateGeneratedPreferencePage copy() {
		return new UltimateGeneratedPreferencePage(mPluginID, mTitle,
				mDefaultPreferences);
	}

	@Override
	protected void createFieldEditors() {

		for (UltimatePreferenceItem item : mDefaultPreferences) {
			switch (item.getType()) {
			case Label:
				createLabel(item.getLabel());
				break;
			case Boolean:
				createBooleanFieldEditor(item.getLabel());
				break;
			case Directory:
				createDirectoryEditor(item.getLabel());
				break;
			case String:
				createStringEditor(item.getLabel());
				break;
			default:
				throw new UnsupportedOperationException(
						"You need to implement the new enum type \""
								+ item.getType() + "\" here");
			}
		}

	}
	
	private void createBooleanFieldEditor(String label) {
		BooleanFieldEditor editor = new BooleanFieldEditor(label, label,
				getFieldEditorParent());
		addField(editor);
	}

	private void createLabel(String label) {
		UltimateLabelFieldEditor editor = new UltimateLabelFieldEditor(label,
				getFieldEditorParent());
		addField(editor);
	}

	private void createDirectoryEditor(String label) {
		DirectoryFieldEditor editor = new DirectoryFieldEditor(label, label,
				getFieldEditorParent());
		addField(editor);
	}

	private void createStringEditor(String label) {
		StringFieldEditor editor = new StringFieldEditor(label, label,
				getFieldEditorParent());
		addField(editor);
	}

	@Override
	public void init(IWorkbench workbench) {
		setPreferenceStore(mPreferenceStore);
		setTitle(mTitle);
	}
	
	@Override
	public boolean performOk() {
		try {
			mPreferenceStore.save();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return super.performOk();
	}

}
