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
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem.Level;
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
			if (prefItem instanceof final UltimatePreferenceItem<?> item) {
				final FieldEditor editor = createFieldEditor(item);

				mMinColumns = Integer.max(mMinColumns, editor.getNumberOfControls());
				final String tooltip = item.getDescription();
				if (tooltip != null) {
					setTooltip(editor, getFieldEditorParent(), tooltip);
				}
				addField(editor);
				if (item.getPreferenceValidator() != null) {
					mCheckedFields.put(editor, item);
				}
			} else if (prefItem instanceof final UltimatePreferenceItemGroup group) {
				beginGroupBox(group.getLabel(), group.getDescription(), 2);
				createFieldEditors(group.getItems());
				endGroupBox();
			}
		}
	}

	private FieldEditor createFieldEditor(final UltimatePreferenceItem<?> item) {
		return switch (item.getType()) {
		case Label -> createLabel(item.getLabel(), item.getLevel());
		case Integer -> createIntegerFieldEditor(item.getLabel(), item.getLevel());
		case Double -> createDoubleFieldEditor(item.getLabel(), item.getLevel());
		case Boolean -> createBooleanFieldEditor(item.getLabel(), item.getLevel());
		case Directory -> createDirectoryEditor(item.getLabel(), item.getLevel());
		case String -> createStringEditor(item.getLabel(), item.getLevel());
		case Combo -> createComboEditor(item, item.getLevel());
		case Radio -> createRadioGroupFieldEditor(item, item.getLevel());
		case Path -> createPathFieldEditor(item, item.getLevel());
		case File -> createFileFieldEditor(item, item.getLevel());
		case MultilineString -> createMultilineFieldEditor(item.getLabel(), item.getLevel());
		case Color -> createColorEditor(item.getLabel(), item.getLevel());
		case KeyValue -> createKeyValueEditor(item.getLabel(), item.getLevel());
		case Group, SubItemContainer -> throw new AssertionError(item.getType() + " should be handled somewhere else");
		};
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
			case Boolean -> validateField((IUltimatePreferenceItemValidator<Boolean>) validator,
					((BooleanFieldEditor) editor).getBooleanValue());
			case Integer -> validateField((IUltimatePreferenceItemValidator<Integer>) validator,
					((IntegerFieldEditor) editor).getIntValue());
			case Double -> validateField((IUltimatePreferenceItemValidator<Double>) validator,
					((DoubleFieldEditor) editor).getDoubleValue());

			case Directory, Path, String, File, Color ->
					validateField((IUltimatePreferenceItemValidator<String>) validator,
							((StringFieldEditor) editor).getStringValue());

			case MultilineString -> validateField((IUltimatePreferenceItemValidator<String>) validator,
					((MultiLineTextFieldEditor) editor).getStringValue());
			case KeyValue -> validateField((IUltimatePreferenceItemValidator<Map<String, String>>) validator,
					((KeyValueGridEditor) editor).getValue());

			case Label, Combo, Radio -> {
				// Label, Combo or Radio cannot be invalid
			}

			case Group, SubItemContainer -> throw new AssertionError("there can be no editor for group or container");
			default -> throw new UnsupportedOperationException(
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

	private String markLabel(final String label, final Level level) {
		if (level == Level.EXPERIMENTAL) {
			return label + " ☢️";
		}
		return label;
	}

	private FieldEditor createColorEditor(final String label, final Level level) {
		return new ColorFieldEditor(label, markLabel(label, level), getFieldEditorParent());
	}

	private FileFieldEditor createFileFieldEditor(final UltimatePreferenceItem<?> item, final Level level) {
		final var label = item.getLabel();
		return new FileFieldEditor(label, markLabel(label, level), getFieldEditorParent());
	}

	private MultiLineTextFieldEditor createMultilineFieldEditor(final String label, final Level level) {
		return new MultiLineTextFieldEditor(label, markLabel(label, level), getFieldEditorParent());
	}

	private PathEditor createPathFieldEditor(final UltimatePreferenceItem<?> item, final Level level) {
		final var label = item.getLabel();
		return new PathEditor(label, markLabel(label, level), item.getLabel(), getFieldEditorParent());
	}

	private RadioGroupFieldEditor createRadioGroupFieldEditor(final UltimatePreferenceItem<?> item, final Level level) {
		final var label = item.getLabel();
		final RadioGroupFieldEditor editor = new RadioGroupFieldEditor(label, markLabel(label, level), 1,
				item.getComboFieldEntries(), getFieldEditorParent());
		editor.loadDefault();
		return editor;
	}

	private ComboFieldEditor createComboEditor(final UltimatePreferenceItem<?> item, final Level level) {
		final var label = item.getLabel();
		return new ComboFieldEditor(label, markLabel(label, level), item.getComboFieldEntries(),
				getFieldEditorParent());
	}

	private IntegerFieldEditor createIntegerFieldEditor(final String label, final Level level) {
		final IntegerFieldEditor editor =
				new IntegerFieldEditor(label, markLabel(label, level), getFieldEditorParent());
		editor.setValidRange(Integer.MIN_VALUE, Integer.MAX_VALUE);
		return editor;
	}

	private DoubleFieldEditor createDoubleFieldEditor(final String label, final Level level) {
		final DoubleFieldEditor editor = new DoubleFieldEditor(label, markLabel(label, level), getFieldEditorParent());
		editor.setValidRange(Double.MIN_VALUE, Double.MAX_VALUE);
		return editor;
	}

	private BooleanFieldEditor createBooleanFieldEditor(final String label, final Level level) {
		return new BooleanFieldEditor(label, markLabel(label, level), getFieldEditorParent());
	}

	private UltimateLabelFieldEditor createLabel(final String label, final Level level) {
		return new UltimateLabelFieldEditor(markLabel(label, level), getFieldEditorParent());
	}

	private DirectoryFieldEditor createDirectoryEditor(final String label, final Level level) {
		return new DirectoryFieldEditor(label, markLabel(label, level), getFieldEditorParent());
	}

	private StringFieldEditor createStringEditor(final String label, final Level level) {
		return new StringFieldEditor(label, markLabel(label, level), getFieldEditorParent());
	}

	private FieldEditor createKeyValueEditor(final String label, final Level level) {
		return new KeyValueGridEditor(label, markLabel(label, level), getFieldEditorParent());
	}
}
