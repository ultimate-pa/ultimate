/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences
 * File:	AbstractDetailsPreferencePage.java created on Feb 5, 2010 by Bjï¿½rn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.gui.preferencepages;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.constants.PreferenceConstants;

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

/**
 * AbstractDetailsPreferencePage
 * 
 * @author Björn Buchhold
 * 
 */
public abstract class AbstractDetailsPreferencePage extends PreferencePage
		implements IWorkbenchPreferencePage {

	// The list that displays the current settings
	private List detailList;
	// The newEntryText is the text where new settings are specified
	private Combo newEntryText;

	// This label can display additional information
	private Label infoLabel;

	/*
	 * @see PreferencePage#createContents(Composite)
	 */
	protected Control createContents(Composite parent) {

		Composite entryTable = new Composite(parent, SWT.NULL);
		// Create a data that takes up the extra space in the dialog .
		GridData data = new GridData(GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = true;
		entryTable.setLayoutData(data);

		GridLayout layout = new GridLayout();
		entryTable.setLayout(layout);

		// Add in a dummy label for spacing
		new Label(entryTable, SWT.NONE);

		detailList = new List(entryTable, SWT.BORDER);
		detailList.setItems(getPreferenceAsStringArray());

		// Create a data that takes up the extra space in the dialog and spans
		// both columns.
		data = new GridData(GridData.FILL_BOTH);
		detailList.setLayoutData(data);

		Composite buttonComposite = new Composite(entryTable, SWT.NULL);

		GridLayout buttonLayout = new GridLayout();
		buttonLayout.numColumns = 2;
		buttonComposite.setLayout(buttonLayout);

		// Create a data that takes up the extra space in the dialog and spans
		// both columns.
		data = new GridData(GridData.FILL_HORIZONTAL
				| GridData.VERTICAL_ALIGN_BEGINNING);
		buttonComposite.setLayoutData(data);

		Button addButton = new Button(buttonComposite, SWT.PUSH | SWT.CENTER);

		addButton.setText("Add to List"); //$NON-NLS-1$
		addButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent event) {
				String text = newEntryText.getText();
				if (entryIsValid(text)) {
					detailList.add(newEntryText.getText(), detailList
							.getItemCount());
					fillInfoLabel(detailList);
				}
			}
		});

		//newEntryText = new Text(buttonComposite, SWT.BORDER);
		newEntryText = new Combo(buttonComposite, SWT.BORDER | SWT.DROP_DOWN);
		// Create a data that takes up the extra space in the dialog .
		data = new GridData(GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = true;
		newEntryText.setLayoutData(data);
		// fill combo with data
		String[] comboContent = getComboSupply();
		for (String s: comboContent) {
			newEntryText.add(s);
		}
		// select first item
		newEntryText.select(0);

		Button removeButton = new Button(buttonComposite, SWT.PUSH | SWT.CENTER);

		removeButton.setText("Remove Selection"); //$NON-NLS-1$
		removeButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent event) {
				detailList.remove(detailList.getSelectionIndex());
				fillInfoLabel(detailList);
			}
		});

		Button editButton = new Button(buttonComposite, SWT.PUSH | SWT.CENTER);
		editButton.setText("Edit Selected"); //$NON-NLS-1$
		editButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent event) {
				String content = detailList.getItem(detailList
						.getSelectionIndex());
				newEntryText.setText(content);
				detailList.remove(detailList.getSelectionIndex());
				fillInfoLabel(detailList);
			}
		});

		// Create a space for additional information
		Composite infoComposite = new Composite(entryTable, SWT.NULL);

		GridLayout infoLayout = new GridLayout();
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
	 * @param detailList 
	 */
	private void fillInfoLabel(List detailList) {
		String content = getInfoContent(detailList);
		infoLabel.setText(content);
	}

	protected abstract String getInfoContent(List detailList);

	private boolean entryIsValid(String text) {
		int eqIndex = text.lastIndexOf("=");
		if (eqIndex <= 0) {
			raiseInvalidEntryError();
			return false;
		}
		String logLevel = text.substring(eqIndex + 1).toUpperCase();

		if (!Arrays.asList(PreferenceConstants.VALUE_VALID_LOG_LEVELS)
				.contains(logLevel)) {
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
		setErrorMessage(PreferenceConstants.INVALID_LOGLEVEL);
	}

	/*
	 * @see IWorkbenchPreferencePage#init(IWorkbench)
	 */
	public void init(IWorkbench workbench) {
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
	protected void performDefaults() {
		detailList.setItems(getDefaults());
	}

	protected abstract String[] getDefaults();

	/**
	 * Method declared on IPreferencePage. Save the author name to the
	 * preference store.
	 */
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
