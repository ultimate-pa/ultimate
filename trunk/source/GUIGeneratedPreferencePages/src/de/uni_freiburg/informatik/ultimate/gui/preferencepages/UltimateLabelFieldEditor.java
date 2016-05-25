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

import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;

/***
 * A field editor for displaying labels not associated with other widgets.
 */
public class UltimateLabelFieldEditor extends FieldEditor {
	/***
	 * Label for this field editor.
	 */
	private Label label;

	/***
	 * All labels can use the same preference name since they don't store any
	 * preference.
	 * 
	 * @param labelText
	 *            text for the label
	 * @param parent
	 *            Composite
	 */
	public UltimateLabelFieldEditor(String labelText, Composite parent) {
		super("label", labelText, parent); //$NON-NLS-1$
	}

	/***
	 * Adjusts the field editor to be displayed correctly for the given number
	 * of columns.
	 * 
	 * @param numColumns
	 *            number of columns
	 */
	@Override
	protected void adjustForNumColumns(int numColumns) {
		((GridData) label.getLayoutData()).horizontalSpan = numColumns;
	}

	/***
	 * Fills the field editor's controls into the given parent.
	 * 
	 * @param parent
	 *            Composite
	 * @param numColumns
	 *            cumber of columns
	 */
	@Override
	protected void doFillIntoGrid(Composite parent, int numColumns) {
		label = getLabelControl(parent);
		final GridData gridData = new GridData();
		gridData.horizontalSpan = numColumns;
		gridData.horizontalAlignment = GridData.FILL;
		gridData.grabExcessHorizontalSpace = false;
		gridData.verticalAlignment = GridData.CENTER;
		gridData.grabExcessVerticalSpace = false;
		label.setLayoutData(gridData);
	}

	/***
	 * Returns the number of controls in the field editor.
	 * 
	 * @return 1
	 */
	@Override
	public int getNumberOfControls() {
		return 1;
	}

	/***
	 * Labels do not persist any preferences, so this method is empty.
	 */
	@Override
	protected void doLoad() {
	}

	/***
	 * Labels do not persist any preferences, so this method is empty.
	 */
	@Override
	protected void doLoadDefault() {
	}

	/***
	 * Labels do not persist any preferences, so this method is empty.
	 */
	@Override
	protected void doStore() {
	}
}
