/*
 * Copyright (C) 2015 Björn Buchhold
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE DebugGUI plug-in.
 * 
 * The ULTIMATE DebugGUI plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE DebugGUI plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE DebugGUI plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE DebugGUI plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE DebugGUI plug-in grant you additional permission
 * to convey the resulting work.
 */
/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.core.model.coreplugin.preferences
 * File:	AbstractDetailsPreferencePage.java created on Feb 5, 2010 by Bjï¿½rn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.gui.preferencepages;

import java.util.Arrays;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.List;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;

/**
 * AbstractDetailsPreferencePage
 * 
 * @author Björn Buchhold
 * 
 */
public abstract class AbstractDetailsPreferencePage extends PreferencePage implements IWorkbenchPreferencePage {

	// The list that displays the current settings
	private List detailList;
	// The newEntryText is the text where new settings are specified
	private Combo newEntryText;

	// This label can display additional information
	private Label infoLabel;

	/*
	 * @see PreferencePage#createContents(Composite)
	 */
	@Override
	protected Control createContents(final Composite parent) {

		final Composite entryTable = new Composite(parent, SWT.NULL);
		// Create a data that takes up the extra space in the dialog .
		GridData data = new GridData(GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = true;
		entryTable.setLayoutData(data);

		final GridLayout layout = new GridLayout();
		entryTable.setLayout(layout);

		// Add in a dummy label for spacing
		new Label(entryTable, SWT.NONE);

		detailList = new List(entryTable, SWT.BORDER);
		detailList.setItems(getPreferenceAsStringArray());

		// Create a data that takes up the extra space in the dialog and spans
		// both columns.
		data = new GridData(GridData.FILL_BOTH);
		detailList.setLayoutData(data);

		final Composite buttonComposite = new Composite(entryTable, SWT.NULL);

		final GridLayout buttonLayout = new GridLayout();
		buttonLayout.numColumns = 2;
		buttonComposite.setLayout(buttonLayout);

		// Create a data that takes up the extra space in the dialog and spans
		// both columns.
		data = new GridData(GridData.FILL_HORIZONTAL | GridData.VERTICAL_ALIGN_BEGINNING);
		buttonComposite.setLayoutData(data);

		final Button addButton = new Button(buttonComposite, SWT.PUSH | SWT.CENTER);

		addButton.setText("Add to List"); //$NON-NLS-1$
		addButton.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(final SelectionEvent event) {
				final String text = newEntryText.getText();
				if (entryIsValid(text)) {
					detailList.add(newEntryText.getText(), detailList.getItemCount());
					fillInfoLabel(detailList);
				}
			}
		});

		// newEntryText = new Text(buttonComposite, SWT.BORDER);
		newEntryText = new Combo(buttonComposite, SWT.BORDER | SWT.DROP_DOWN);
		// Create a data that takes up the extra space in the dialog .
		data = new GridData(GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = true;
		newEntryText.setLayoutData(data);
		// fill combo with data
		final String[] comboContent = getComboSupply();
		for (final String s : comboContent) {
			newEntryText.add(s);
		}
		// select first item
		newEntryText.select(0);

		final Button removeButton = new Button(buttonComposite, SWT.PUSH | SWT.CENTER);

		removeButton.setText("Remove Selection"); //$NON-NLS-1$
		removeButton.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(final SelectionEvent event) {
				detailList.remove(detailList.getSelectionIndex());
				fillInfoLabel(detailList);
			}
		});

		final Button editButton = new Button(buttonComposite, SWT.PUSH | SWT.CENTER);
		editButton.setText("Edit Selected"); //$NON-NLS-1$
		editButton.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(final SelectionEvent event) {
				final int index = detailList.getSelectionIndex();
				if (index == -1) {
					return;
				}
				final String content = detailList.getItem(index);
				newEntryText.setText(content);
				detailList.remove(detailList.getSelectionIndex());
				fillInfoLabel(detailList);
			}
		});

		// Create a space for additional information
		final Composite infoComposite = new Composite(entryTable, SWT.NULL);

		final GridLayout infoLayout = new GridLayout();
		infoLayout.numColumns = 1;
		infoComposite.setLayout(infoLayout);
		data = new GridData(GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = true;
		infoComposite.setLayoutData(data);

		infoLabel = new Label(infoComposite, SWT.WRAP | SWT.BORDER);
		infoLabel.setBounds(infoComposite.getBounds());
		data = new GridData(GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = true;
		infoLabel.setLayoutData(data);

		fillInfoLabel(detailList);

		return entryTable;
	}

	protected abstract String[] getComboSupply();

	/**
	 * void fillInfoLabel
	 * 
	 * @param detailList
	 */
	private void fillInfoLabel(final List detailList) {
		final String content = getInfoContent(detailList);
		infoLabel.setText(content);
	}

	protected abstract String getInfoContent(List detailList);

	private boolean entryIsValid(final String text) {
		final int eqIndex = text.lastIndexOf('=');
		if (eqIndex <= 0) {
			raiseInvalidEntryError();
			return false;
		}
		final String logLevel = text.substring(eqIndex + 1).toUpperCase();

		if (!Arrays.asList(CorePreferenceInitializer.VALUE_VALID_LOG_LEVELS).contains(logLevel)) {
			raiseInvalidLogLevelError();
			return false;
		}
		setErrorMessage(null);
		return true;
	}

	/**
	 * void raiseInvalidEntryError
	 */
	private void raiseInvalidEntryError() {
		setErrorMessage(getInvalidEntryMessage());
	}

	/**
	 * String getInvalidEntryMessage
	 * 
	 * @return Message for an invalid entry.
	 */
	protected abstract String getInvalidEntryMessage();

	/**
	 * void raiseInvalidLogLevelError
	 */
	private void raiseInvalidLogLevelError() {
		setErrorMessage(CorePreferenceInitializer.INVALID_LOGLEVEL);
	}

	/*
	 * @see IWorkbenchPreferencePage#init(IWorkbench)
	 */
	@Override
	public void init(final IWorkbench workbench) {
		// Initialize the preference store we wish to use
		setPreferenceStore(getCorrectPreferenceStore());
	}

	/**
	 * IPreferenceStore getCorrectPreferenceStore
	 * 
	 * @return Preference Store to use.
	 */
	protected abstract IPreferenceStore getCorrectPreferenceStore();

	/**
	 * Performs special processing when this page's Restore Defaults button has
	 * been pressed. Sets the contents of the nameEntry field to be the default
	 */
	@Override
	protected void performDefaults() {
		detailList.setItems(getDefaults());
	}

	protected abstract String[] getDefaults();

	/**
	 * Method declared on IPreferencePage. Save the author name to the
	 * preference store.
	 */
	@Override
	public boolean performOk() {
		setThePreference(detailList.getItems());
		return super.performOk();
	}

	/**
	 * void setThePreference
	 * 
	 * @param items
	 */
	protected abstract void setThePreference(String[] items);

	/**
	 * String[] getPreferenceAsStringArray
	 * 
	 * @return Preference converted into an array of Strings.
	 */
	protected abstract String[] getPreferenceAsStringArray();

}
