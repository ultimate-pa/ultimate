/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE GUIGeneratedPreferencePages plug-in.
 * 
 * The ULTIMATE GUIGeneratedPreferencePages plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE GUIGeneratedPreferencePages plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE GUIGeneratedPreferencePages plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE GUIGeneratedPreferencePages plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE GUIGeneratedPreferencePages plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.gui.preferencepages;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ColorFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.DirectoryFieldEditor;
import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.FileFieldEditor;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.jface.preference.PathEditor;
import org.eclipse.jface.preference.RadioGroupFieldEditor;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.gui.customeditors.MultiLineTextFieldEditor;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class UltimateGeneratedPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {

	private final String mPluginID;
	private final BaseUltimatePreferenceItem[] mDefaultPreferences;
	private final String mTitle;
	private final ScopedPreferenceStore mPreferenceStore;
	private final Map<FieldEditor, UltimatePreferenceItem<?>> mCheckedFields;

	public UltimateGeneratedPreferencePage(String pluginID, String title, BaseUltimatePreferenceItem[] preferences) {
		super(GRID);
		mPluginID = pluginID;
		mDefaultPreferences = preferences;
		mTitle = title;
		mPreferenceStore = new ScopedPreferenceStore(new RcpPreferenceProvider(mPluginID).getScopeContext(),
				mPluginID);
		mCheckedFields = new HashMap<FieldEditor, UltimatePreferenceItem<?>>();
		setPreferenceStore(mPreferenceStore);
		setTitle(mTitle);
	}

	public UltimateGeneratedPreferencePage copy() {
		return new UltimateGeneratedPreferencePage(mPluginID, mTitle, mDefaultPreferences);
	}

	@Override
	protected void createFieldEditors() {
		for (final BaseUltimatePreferenceItem prefItem : mDefaultPreferences) {
			if (prefItem instanceof UltimatePreferenceItem) {
				final UltimatePreferenceItem<?> item = (UltimatePreferenceItem<?>) prefItem;
				final FieldEditor editor;
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
				case File:
					editor = createFileFieldEditor(item);
					break;
				case MultilineString:
					editor = createMultilineFieldEditor(item.getLabel());
					break;
				case Color:
					editor = createColorEditor(item.getLabel());
					break;
				default:
					throw new UnsupportedOperationException(
					        "You need to implement the new enum type \"" + item.getType() + "\" here");
				}

				final String tooltip = item.getToolTip();
				if (tooltip != null) {
					setTooltip(editor, getFieldEditorParent(), tooltip);
				}
				addField(editor);
				if (item.getPreferenceValidator() != null) {
					mCheckedFields.put(editor, item);
				}
			}
		}
	}

	private void setTooltip(final FieldEditor editor, final Composite parent, final String tooltip) {
		if (editor instanceof BooleanFieldEditor) {
			((BooleanFieldEditor) editor).getDescriptionControl(parent).setToolTipText(tooltip);
		} else {
			final Label label = editor.getLabelControl(parent);
			label.setToolTipText(tooltip);
		}
	}

	@Override
	protected void checkState() {
		super.checkState();
		if (isValid()) {
			for (final FieldEditor entry : mCheckedFields.keySet()) {
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
		} catch (final IOException e) {
			e.printStackTrace();
		}
		return super.performOk();
	}

	@SuppressWarnings("unchecked")
	private void checkState(FieldEditor editor) {
		if (editor.isValid()) {
			final UltimatePreferenceItem<?> preferenceDescriptor = mCheckedFields.get(editor);
			if (preferenceDescriptor == null) {
				return;
			}
			final IUltimatePreferenceItemValidator<?> validator = preferenceDescriptor.getPreferenceValidator();
			switch (preferenceDescriptor.getType()) {
			case Boolean:
				validateField((IUltimatePreferenceItemValidator<Boolean>) validator,
						((BooleanFieldEditor) editor).getBooleanValue());
				break;
			case Integer:
				validateField((IUltimatePreferenceItemValidator<Integer>) validator,
						((IntegerFieldEditor) editor).getIntValue());
				break;
			case Directory:
			case Path:
			case String:
			case File:
			case Color:
				validateField((IUltimatePreferenceItemValidator<String>) validator,
						((StringFieldEditor) editor).getStringValue());
				break;
			case MultilineString:
				validateField((IUltimatePreferenceItemValidator<String>) validator,
						((MultiLineTextFieldEditor) editor).getStringValue());
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
						"You need to implement the new enum type \"" + preferenceDescriptor.getType() + "\" here");
			}
		}
	}

	private <T> void validateField(IUltimatePreferenceItemValidator<T> validator, T value) {
		if (!validator.isValid(value)) {
			setErrorMessage(validator.getInvalidValueErrorMessage(value));
			setValid(false);
		} else {
			setErrorMessage(null);
			setValid(true);
		}
	}

	private FieldEditor createColorEditor(String label) {
		return new ColorFieldEditor(label, label, getFieldEditorParent());
	}

	private FileFieldEditor createFileFieldEditor(UltimatePreferenceItem<?> item) {
		return new FileFieldEditor(item.getLabel(), item.getLabel(), getFieldEditorParent());
	}

	private MultiLineTextFieldEditor createMultilineFieldEditor(String label) {
		return new MultiLineTextFieldEditor(label, label, getFieldEditorParent());
	}

	private PathEditor createPathFieldEditor(UltimatePreferenceItem<?> item) {
		return new PathEditor(item.getLabel(), item.getLabel(), item.getLabel(), getFieldEditorParent());
	}

	private RadioGroupFieldEditor createRadioGroupFieldEditor(UltimatePreferenceItem<?> item) {
		final RadioGroupFieldEditor editor = new RadioGroupFieldEditor(item.getLabel(), item.getLabel(), 1,
				item.getComboFieldEntries(), getFieldEditorParent());
		editor.loadDefault();
		return editor;
	}

	private ComboFieldEditor createComboEditor(UltimatePreferenceItem<?> item) {
		return new ComboFieldEditor(item.getLabel(), item.getLabel(), item.getComboFieldEntries(),
				getFieldEditorParent());
	}

	private IntegerFieldEditor createIntegerFieldEditor(String label) {
		final IntegerFieldEditor editor = new IntegerFieldEditor(label, label, getFieldEditorParent());
		editor.setValidRange(Integer.MIN_VALUE, Integer.MAX_VALUE);
		return editor;
	}

	private BooleanFieldEditor createBooleanFieldEditor(String label) {
		return new BooleanFieldEditor(label, label, getFieldEditorParent());
	}

	private UltimateLabelFieldEditor createLabel(String label) {
		return new UltimateLabelFieldEditor(label, getFieldEditorParent());
	}

	private DirectoryFieldEditor createDirectoryEditor(String label) {
		return new DirectoryFieldEditor(label, label, getFieldEditorParent());
	}

	private StringFieldEditor createStringEditor(String label) {
		return new StringFieldEditor(label, label, getFieldEditorParent());
	}
}
