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
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ColorFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.DirectoryFieldEditor;
import org.eclipse.jface.preference.DoubleFieldEditor;
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
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemGroup;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.gui.customeditors.KeyValueGridEditor;
import de.uni_freiburg.informatik.ultimate.gui.customeditors.MultiLineTextFieldEditor;
import de.uni_freiburg.informatik.ultimate.gui.customeditors.UltimateLabelFieldEditor;

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

	private final ArrayDeque<ItemGroupBox> mActiveGroups = new ArrayDeque<>();
	private final List<ItemGroupBox> mGroups = new ArrayList<>();
	private int mMinColumns = 0;

	public UltimateGeneratedPreferencePage(final String pluginID, final String title,
			final BaseUltimatePreferenceItem[] preferences) {
		super(GRID);
		mPluginID = pluginID;
		mDefaultPreferences = preferences;
		mTitle = title;
		mPreferenceStore = new ScopedPreferenceStore(new RcpPreferenceProvider(mPluginID).getScopeContext(), mPluginID);
		mCheckedFields = new HashMap<>();
		setPreferenceStore(mPreferenceStore);
		setTitle(mTitle);
	}

	public UltimateGeneratedPreferencePage copy() {
		return new UltimateGeneratedPreferencePage(mPluginID, mTitle, mDefaultPreferences);
	}

	@Override
	protected void createFieldEditors() {
		createFieldEditors(Arrays.asList(mDefaultPreferences));
		adjustGroupGrids();
	}

	protected void createFieldEditors(final List<BaseUltimatePreferenceItem> items) {
		for (final BaseUltimatePreferenceItem prefItem : items) {
			if (prefItem instanceof UltimatePreferenceItem) {
				final UltimatePreferenceItem<?> item = (UltimatePreferenceItem<?>) prefItem;
				final FieldEditor editor;
				switch (item.getType()) {
				case Label:
					editor = createLabel(item.getLabel(), item.isExperimental());
					break;
				case Integer:
					editor = createIntegerFieldEditor(item.getLabel(), item.isExperimental());
					break;
				case Double:
					editor = createDoubleFieldEditor(item.getLabel(), item.isExperimental());
					break;
				case Boolean:
					editor = createBooleanFieldEditor(item.getLabel(), item.isExperimental());
					break;
				case Directory:
					editor = createDirectoryEditor(item.getLabel(), item.isExperimental());
					break;
				case String:
					editor = createStringEditor(item.getLabel(), item.isExperimental());
					break;
				case Combo:
					editor = createComboEditor(item, item.isExperimental());
					break;
				case Radio:
					editor = createRadioGroupFieldEditor(item, item.isExperimental());
					break;
				case Path:
					editor = createPathFieldEditor(item, item.isExperimental());
					break;
				case File:
					editor = createFileFieldEditor(item, item.isExperimental());
					break;
				case MultilineString:
					editor = createMultilineFieldEditor(item.getLabel(), item.isExperimental());
					break;
				case Color:
					editor = createColorEditor(item.getLabel(), item.isExperimental());
					break;
				case KeyValue:
					editor = createKeyValueEditor(item.getLabel(), item.isExperimental());
					break;
				default:
					throw new UnsupportedOperationException(
							"You need to implement the new enum type \"" + item.getType() + "\" here");
				}

				mMinColumns = Integer.max(mMinColumns, editor.getNumberOfControls());
				final String tooltip = item.getDescription();
				if (tooltip != null) {
					setTooltip(editor, getFieldEditorParent(), tooltip);
				}
				addField(editor);
				if (item.getPreferenceValidator() != null) {
					mCheckedFields.put(editor, item);
				}
			} else if (prefItem instanceof UltimatePreferenceItemGroup) {
				final var group = (UltimatePreferenceItemGroup) prefItem;
				beginGroupBox(group.getLabel(), group.getDescription(), 2);
				createFieldEditors(group.getItems());
				endGroupBox();
			}
		}
	}

	protected void adjustGroupGrids() {
		for (final var group : mGroups) {
			group.adjustForNumColumns(mMinColumns);
		}
	}

	private static void setTooltip(final FieldEditor editor, final Composite parent, final String tooltip) {
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
	public void propertyChange(final PropertyChangeEvent event) {
		super.propertyChange(event);
		if (event.getProperty().equals(FieldEditor.VALUE)) {
			checkState((FieldEditor) event.getSource());
		}
	}

	@Override
	public void init(final IWorkbench workbench) {
		// not needed
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

	private void beginGroupBox(final String label, final String description, final int numColumns) {
		mActiveGroups.push(new ItemGroupBox(label, description, getFieldEditorParent(), numColumns));
	}

	private void endGroupBox() {
		final var finished = mActiveGroups.pop();
		mGroups.add(finished);
	}

	@Override
	protected Composite getFieldEditorParent() {
		if (mActiveGroups.isEmpty()) {
			return super.getFieldEditorParent();
		}
		final var topGroup = mActiveGroups.peek();
		return topGroup.getFieldEditorParent();
	}

	@SuppressWarnings("unchecked")
	private void checkState(final FieldEditor editor) {
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
			case Double:
				validateField((IUltimatePreferenceItemValidator<Double>) validator,
						((DoubleFieldEditor) editor).getDoubleValue());
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
			case KeyValue:
				validateField((IUltimatePreferenceItemValidator<Map<String, String>>) validator,
						((KeyValueGridEditor) editor).getValue());
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

	private <T> void validateField(final IUltimatePreferenceItemValidator<T> validator, final T value) {
		if (!validator.isValid(value)) {
			setErrorMessage(validator.getInvalidValueErrorMessage(value));
			setValid(false);
		} else {
			setErrorMessage(null);
			setValid(true);
		}
	}

	private String markLabel(final String label, final boolean experimental) {
		if (experimental) {
			return label + " ☢️";
		}
		return label;
	}

	private FieldEditor createColorEditor(final String label, final boolean experimental) {
		return new ColorFieldEditor(label, markLabel(label, experimental), getFieldEditorParent());
	}

	private FileFieldEditor createFileFieldEditor(final UltimatePreferenceItem<?> item, final boolean experimental) {
		final var label = item.getLabel();
		return new FileFieldEditor(label, markLabel(label, experimental), getFieldEditorParent());
	}

	private MultiLineTextFieldEditor createMultilineFieldEditor(final String label, final boolean experimental) {
		return new MultiLineTextFieldEditor(label, markLabel(label, experimental), getFieldEditorParent());
	}

	private PathEditor createPathFieldEditor(final UltimatePreferenceItem<?> item, final boolean experimental) {
		final var label = item.getLabel();
		return new PathEditor(label, markLabel(label, experimental), item.getLabel(), getFieldEditorParent());
	}

	private RadioGroupFieldEditor createRadioGroupFieldEditor(final UltimatePreferenceItem<?> item,
			final boolean experimental) {
		final var label = item.getLabel();
		final RadioGroupFieldEditor editor = new RadioGroupFieldEditor(label, markLabel(label, experimental), 1,
				item.getComboFieldEntries(), getFieldEditorParent());
		editor.loadDefault();
		return editor;
	}

	private ComboFieldEditor createComboEditor(final UltimatePreferenceItem<?> item, final boolean experimental) {
		final var label = item.getLabel();
		return new ComboFieldEditor(label, markLabel(label, experimental), item.getComboFieldEntries(),
				getFieldEditorParent());
	}

	private IntegerFieldEditor createIntegerFieldEditor(final String label, final boolean experimental) {
		final IntegerFieldEditor editor =
				new IntegerFieldEditor(label, markLabel(label, experimental), getFieldEditorParent());
		editor.setValidRange(Integer.MIN_VALUE, Integer.MAX_VALUE);
		return editor;
	}

	private DoubleFieldEditor createDoubleFieldEditor(final String label, final boolean experimental) {
		final DoubleFieldEditor editor =
				new DoubleFieldEditor(label, markLabel(label, experimental), getFieldEditorParent());
		editor.setValidRange(Double.MIN_VALUE, Double.MAX_VALUE);
		return editor;
	}

	private BooleanFieldEditor createBooleanFieldEditor(final String label, final boolean experimental) {
		return new BooleanFieldEditor(label, markLabel(label, experimental), getFieldEditorParent());
	}

	private UltimateLabelFieldEditor createLabel(final String label, final boolean experimental) {
		return new UltimateLabelFieldEditor(markLabel(label, experimental), getFieldEditorParent());
	}

	private DirectoryFieldEditor createDirectoryEditor(final String label, final boolean experimental) {
		return new DirectoryFieldEditor(label, markLabel(label, experimental), getFieldEditorParent());
	}

	private StringFieldEditor createStringEditor(final String label, final boolean experimental) {
		return new StringFieldEditor(label, markLabel(label, experimental), getFieldEditorParent());
	}

	private FieldEditor createKeyValueEditor(final String label, final boolean experimental) {
		return new KeyValueGridEditor(label, markLabel(label, experimental), getFieldEditorParent());
	}
}
