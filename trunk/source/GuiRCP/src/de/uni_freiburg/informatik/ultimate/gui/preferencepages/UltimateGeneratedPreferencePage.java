package de.uni_freiburg.informatik.ultimate.gui.preferencepages;

import java.io.IOException;
import java.util.HashMap;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.DirectoryFieldEditor;
import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.jface.preference.PathEditor;
import org.eclipse.jface.preference.RadioGroupFieldEditor;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;

public class UltimateGeneratedPreferencePage extends FieldEditorPreferencePage
		implements IWorkbenchPreferencePage {

	private String mPluginID;
	private UltimatePreferenceItem<?>[] mDefaultPreferences;
	private String mTitle;
	private ScopedPreferenceStore mPreferenceStore;
	private HashMap<FieldEditor, UltimatePreferenceItem<?>> mCheckedFields;

	public UltimateGeneratedPreferencePage(String pluginID, String title,
			UltimatePreferenceItem<?>[] preferences) {
		super(GRID);
		mPluginID = pluginID;
		mDefaultPreferences = preferences;
		mTitle = title;
		mPreferenceStore = new ScopedPreferenceStore(
				new UltimatePreferenceStore(mPluginID).getScopeContext(),
				mPluginID);
		mCheckedFields = new HashMap<FieldEditor, UltimatePreferenceItem<?>>();
		setPreferenceStore(mPreferenceStore);
		setTitle(mTitle);
	}

	public UltimateGeneratedPreferencePage copy() {
		return new UltimateGeneratedPreferencePage(mPluginID, mTitle,
				mDefaultPreferences);
	}

	@Override
	protected void createFieldEditors() {

		for (UltimatePreferenceItem<?> item : mDefaultPreferences) {
			FieldEditor editor;
			switch (item.getType()) {
			case Label:
				editor = createLabel(item.getLabel());
				break;
			case Integer:
				editor = createIntegerFieldEditor(item.getLabel());
				break;
			case Boolean:
				editor = createBooleanFieldEditor(item.getLabel());
				break;
			case Directory:
				editor = createDirectoryEditor(item.getLabel());
				break;
			case String:
				editor = createStringEditor(item.getLabel());
				break;
			case Combo:
				editor = createComboEditor(item);
				break;
			case Radio:
				editor = createRadioGroupFieldEditor(item);
				break;
			case Path:
				editor = createPathFieldEditor(item);
				break;
			case MultilineString:
				editor = createMultilineFieldEditor(item.getLabel());
				break;
			default:
				throw new UnsupportedOperationException(
						"You need to implement the new enum type \""
								+ item.getType() + "\" here");
			}

			if (item.getPreferenceValidator() != null && editor != null) {
				mCheckedFields.put(editor, item);
			}
		}

	}



	@Override
	protected void checkState() {
		super.checkState();
		if (isValid()) {
			for (FieldEditor entry : mCheckedFields.keySet()) {
				checkState(entry);
			}
		}
	}

	@Override
	public void propertyChange(PropertyChangeEvent event) {
		super.propertyChange(event);
		if (event.getProperty().equals(FieldEditor.VALUE)) {
			checkState((FieldEditor) event.getSource());
		}
	}

	@Override
	public void init(IWorkbench workbench) {

	}

	@Override
	public boolean performOk() {
		try {
			mPreferenceStore.save();
		} catch (IOException e) {
			e.printStackTrace();
		}
		return super.performOk();
	}

	private void checkState(FieldEditor editor) {
		if (editor.isValid()) {
			UltimatePreferenceItem<?> preferenceDescriptor = mCheckedFields
					.get(editor);
			if (preferenceDescriptor == null) {
				return;
			}
			IUltimatePreferenceItemValidator<?> validator = preferenceDescriptor
					.getPreferenceValidator();
			switch (preferenceDescriptor.getType()) {
			case Boolean:
				validateField(
						(IUltimatePreferenceItemValidator<Boolean>) validator,
						((BooleanFieldEditor) editor).getBooleanValue());
				break;
			case Integer:
				validateField(
						(IUltimatePreferenceItemValidator<Integer>) validator,
						((IntegerFieldEditor) editor).getIntValue());
				break;
			case Directory:
			case Path:
			case String:
				validateField(
						(IUltimatePreferenceItemValidator<String>) validator,
						((StringFieldEditor) editor).getStringValue());
				break;
			
			case Label:
			case Combo:
			case Radio:
				// Label cannot be invalid
				// Combo cannot be invalid
				// Radio cannot be invalid
				break;
			default:
				throw new UnsupportedOperationException(
						"You need to implement the new enum type \""
								+ preferenceDescriptor.getType() + "\" here");
			}
		}
	}

	private <T> void validateField(
			IUltimatePreferenceItemValidator<T> validator, T value) {
		if (!validator.isValid(value)) {
			setErrorMessage(validator.getInvalidValueErrorMessage(value));
			setValid(false);
		} else {
			setErrorMessage(null);
			setValid(true);
		}
	}

	private MultiLineTextFieldEditor createMultilineFieldEditor(String label) {
		MultiLineTextFieldEditor editor = new MultiLineTextFieldEditor(label,label,getFieldEditorParent());
		addField(editor);
		return editor;
	}
	
	private PathEditor createPathFieldEditor(UltimatePreferenceItem<?> item) {
		PathEditor editor = new PathEditor(item.getLabel(), item.getLabel(),
				item.getLabel(), getFieldEditorParent());
		addField(editor);
		return editor;
	}

	private RadioGroupFieldEditor createRadioGroupFieldEditor(
			UltimatePreferenceItem<?> item) {
		RadioGroupFieldEditor editor = new RadioGroupFieldEditor(
				item.getLabel(), item.getLabel(), 1,
				item.getComboFieldEntries(), getFieldEditorParent());
		editor.loadDefault();
		addField(editor);
		return editor;
	}

	private ComboFieldEditor createComboEditor(UltimatePreferenceItem<?> item) {
		ComboFieldEditor comboEditor = new ComboFieldEditor(item.getLabel(),
				item.getLabel(), item.getComboFieldEntries(),
				getFieldEditorParent());
		addField(comboEditor);
		return comboEditor;
	}

	private IntegerFieldEditor createIntegerFieldEditor(String label) {
		IntegerFieldEditor editor = new IntegerFieldEditor(label, label,
				getFieldEditorParent());
		editor.setValidRange(Integer.MIN_VALUE, Integer.MAX_VALUE);
		addField(editor);
		return editor;
	}

	private BooleanFieldEditor createBooleanFieldEditor(String label) {
		BooleanFieldEditor editor = new BooleanFieldEditor(label, label,
				getFieldEditorParent());
		addField(editor);
		return editor;
	}

	private UltimateLabelFieldEditor createLabel(String label) {
		UltimateLabelFieldEditor editor = new UltimateLabelFieldEditor(label,
				getFieldEditorParent());
		addField(editor);
		return editor;
	}

	private DirectoryFieldEditor createDirectoryEditor(String label) {
		DirectoryFieldEditor editor = new DirectoryFieldEditor(label, label,
				getFieldEditorParent());
		addField(editor);
		return editor;
	}

	private StringFieldEditor createStringEditor(String label) {
		StringFieldEditor editor = new StringFieldEditor(label, label,
				getFieldEditorParent());
		
		addField(editor);
		return editor;
	}

}
