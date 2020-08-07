/*
 * Copyright (C) 2020 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.gui.customeditors;

import java.util.Arrays;
import java.util.Collections;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.viewers.CellEditor;
import org.eclipse.jface.viewers.ICellModifier;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TableViewerColumn;
import org.eclipse.jface.viewers.TextCellEditor;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.ScrolledComposite;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.ui.internal.dialogs.ViewComparator;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.KeyValueUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
@SuppressWarnings("restriction")
public final class KeyValueGridEditor extends FieldEditor {

	private static final String COL_KEY_NAME = "Key";
	private static final String COL_VAL_NAME = "Value";

	private static final int COL_KEY_WIDTH = 400;
	private static final int COL_VAL_WIDTH = 200;

	private Map<String, String> mKeyValueModel;
	private TableViewer mTableViewer;
	private Composite mEditorParent;

	public KeyValueGridEditor(final String name, final String labelText, final Composite parent) {
		init(name, labelText);
		createControl(parent);
	}

	@Override
	protected void adjustForNumColumns(final int numColumns) {
		if (mEditorParent != null) {
			final GridData gd = (GridData) mEditorParent.getLayoutData();
			gd.horizontalSpan = numColumns - 1;
		}
	}

	private static GridLayout createGridLayout() {
		final GridLayout gl = new GridLayout();
		gl.horizontalSpacing = 0;
		gl.marginWidth = 0;
		return gl;
	}

	@Override
	protected void doFillIntoGrid(final Composite parent, final int numColumns) {
		final Composite labelParent = new Composite(parent, SWT.NONE);
		labelParent.setLayout(createGridLayout());
		labelParent.setLayoutData(new GridData(SWT.FILL, SWT.BEGINNING, true, false));
		getLabelControl(labelParent);

		mEditorParent = new Composite(parent, SWT.NONE);
		mEditorParent.setLayout(createGridLayout());
		mEditorParent.setLayoutData(new GridData(SWT.FILL, SWT.BEGINNING, true, false, numColumns - 1, 1));

		mTableViewer = new TableViewer(mEditorParent, SWT.BORDER | SWT.FULL_SELECTION | SWT.MULTI);

		final TableViewerColumn colKey = new TableViewerColumn(mTableViewer, SWT.NONE);
		colKey.getColumn().setWidth(COL_KEY_WIDTH);
		colKey.getColumn().setText(COL_KEY_NAME);
		colKey.getColumn().addSelectionListener(new SelectionAdapter() {

			@Override
			public void widgetSelected(final SelectionEvent e) {
				mTableViewer.setComparator(new KeyValueViewerSorter(0));
			}
		});

		final TableViewerColumn colValue = new TableViewerColumn(mTableViewer, SWT.NONE);
		colValue.getColumn().setWidth(COL_VAL_WIDTH);
		colValue.getColumn().setText(COL_VAL_NAME);
		colValue.getColumn().addSelectionListener(new SelectionAdapter() {

			@Override
			public void widgetSelected(final SelectionEvent e) {
				mTableViewer.setComparator(new KeyValueViewerSorter(1));
			}
		});

		mTableViewer.setContentProvider(new MapContentProvider());
		mTableViewer.setLabelProvider(new KeyValueLabelProvider());
		mTableViewer.setColumnProperties(new String[] { COL_KEY_NAME, COL_VAL_NAME });
		mTableViewer.setCellEditors(new CellEditor[] { new TextCellEditor(mTableViewer.getTable()),
				new TextCellEditor(mTableViewer.getTable()) });

		mTableViewer.setCellModifier(new KeyValueCellModifier());

		mTableViewer.getTable().setHeaderVisible(true);
		mTableViewer.getTable().setLinesVisible(true);

		final Composite buttonParent = new Composite(mEditorParent, SWT.NULL);
		buttonParent.setLayout(new GridLayout(2, false));
		buttonParent.setLayoutData(new GridData(SWT.FILL, SWT.BEGINNING, true, false));

		final Button addButton = new Button(buttonParent, SWT.PUSH | SWT.CENTER);
		addButton.setText("Add");
		addButton.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(final SelectionEvent event) {
				final Pair<String, String> newElem = new Pair<>("", "");
				final String old = mKeyValueModel.put(newElem.getKey(), newElem.getValue());
				if (old == null) {
					mTableViewer.add(newElem);
					mTableViewer.setSelection(new StructuredSelection(newElem));
					pack();
				}
			}
		});

		final Button removeButton = new Button(buttonParent, SWT.PUSH | SWT.CENTER);

		removeButton.setText("Remove");
		removeButton.addSelectionListener(new SelectionAdapter() {
			@SuppressWarnings("unchecked")
			@Override
			public void widgetSelected(final SelectionEvent event) {
				final ISelection selection = mTableViewer.getSelection();
				if (selection instanceof StructuredSelection) {
					final Object[] selectedPairs = ((StructuredSelection) selection).toArray();
					Arrays.stream(selectedPairs).map(a -> (Entry<String, String>) a)
							.forEach(a -> mKeyValueModel.remove(a.getKey()));
					mTableViewer.remove(selectedPairs);
					pack();
				}
			}
		});
	}

	private void pack() {
		Composite p = mTableViewer.getTable();
		while (p != null && !(p instanceof ScrolledComposite)) {
			p.pack();
			p = p.getParent();
		}
	}

	@Override
	protected void doLoad() {
		load(getPreferenceStore().getString(getPreferenceName()));
	}

	@Override
	protected void doLoadDefault() {
		load(getPreferenceStore().getDefaultString(getPreferenceName()));
	}

	private void load(final String value) {
		mKeyValueModel = KeyValueUtil.toMap(value);
		mTableViewer.setInput(mKeyValueModel);
	}

	@Override
	protected void doStore() {
		getPreferenceStore().setValue(getPreferenceName(), KeyValueUtil.toKeyValueString(mKeyValueModel));
	}

	@Override
	public int getNumberOfControls() {
		return 1;
	}

	public Map<String, String> getValue() {
		return Collections.unmodifiableMap(mKeyValueModel);
	}

	private static final class MapContentProvider implements IStructuredContentProvider {

		private static final Object[] EMPTY = new Object[0];

		@Override
		public Object[] getElements(final Object inputElement) {
			if (inputElement instanceof Map) {
				@SuppressWarnings("unchecked")
				final Map<String, String> map = (Map<String, String>) inputElement;
				final Set<Entry<String, String>> entries = map.entrySet();
				return entries.toArray(new Entry[entries.size()]);
			}
			return EMPTY;
		}

		@Override
		public void dispose() {
			// not needed
		}

		@Override
		public void inputChanged(final Viewer viewer, final Object oldInput, final Object newInput) {
			// not needed
		}

	}

	private static final class KeyValueLabelProvider extends LabelProvider implements ITableLabelProvider {

		@Override
		public Image getColumnImage(final Object element, final int columnIndex) {
			return null;
		}

		@Override
		public String getColumnText(final Object element, final int columnIndex) {
			@SuppressWarnings("unchecked")
			final Entry<String, String> entry = (Entry<String, String>) element;
			switch (columnIndex) {
			case 0:
				return entry.getKey();
			case 1:
				return entry.getValue();
			default:
				throw new IllegalArgumentException("Only two columns allowed");
			}
		}

	}

	private static final class KeyValueViewerSorter extends ViewComparator {

		private final int mIdx;

		public KeyValueViewerSorter(final int column) {
			mIdx = column;
		}

		@Override
		public int compare(final Viewer viewer, final Object e1, final Object e2) {
			@SuppressWarnings("unchecked")
			final Entry<String, String> en1 = (Entry<String, String>) e1;
			@SuppressWarnings("unchecked")
			final Entry<String, String> en2 = (Entry<String, String>) e2;
			switch (mIdx) {
			case 0:
				return super.compare(viewer, en1.getKey(), en2.getKey());
			case 1:
				return super.compare(viewer, en1.getValue(), en2.getValue());
			default:
				throw new IllegalArgumentException("Only columns key and value are supported");
			}

		}
	}

	private final class KeyValueCellModifier implements ICellModifier {

		@Override
		public boolean canModify(final Object element, final String property) {
			return true;
		}

		@Override
		public Object getValue(final Object element, final String property) {
			@SuppressWarnings("unchecked")
			final Entry<String, String> entry = (Entry<String, String>) element;
			switch (property) {
			case COL_KEY_NAME:
				return entry.getKey();
			case COL_VAL_NAME:
				return entry.getValue();
			default:
				throw new IllegalArgumentException("Unknown column " + property);
			}
		}

		@Override
		public void modify(final Object element, final String property, final Object value) {
			final TableItem item = (TableItem) element;
			@SuppressWarnings("unchecked")
			final Entry<String, String> oldEntry = (Entry<String, String>) item.getData();
			final Entry<String, String> newEntry;
			final String strValue = (String) value;
			switch (property) {
			case COL_KEY_NAME:
				newEntry = new Pair<>(strValue, oldEntry.getValue());
				break;
			case COL_VAL_NAME:
				newEntry = new Pair<>(oldEntry.getKey(), strValue);
				break;
			default:
				throw new IllegalArgumentException("Unknown column " + property);
			}

			if (oldEntry.getKey() != newEntry.getKey() && mKeyValueModel.containsKey(newEntry.getKey())) {
				// ignore edit if user wants to add key duplicate
				return;
			}
			if (!KeyValueUtil.isValid(newEntry)) {
				// ignore edit if user wants to add illegal value
				return;
			}
			mKeyValueModel.remove(oldEntry.getKey());
			mKeyValueModel.put(newEntry.getKey(), newEntry.getValue());
			item.setData(newEntry);
			mTableViewer.update(newEntry, null);
		}

	}

}
