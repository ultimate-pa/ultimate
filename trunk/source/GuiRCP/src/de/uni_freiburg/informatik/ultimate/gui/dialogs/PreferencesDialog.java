/*
 * Copyright (C) 2008-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.gui.dialogs;

import java.util.prefs.Preferences;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Dialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;

import de.uni_freiburg.informatik.ultimate.gui.GuiController;

public class PreferencesDialog extends Dialog {

	public static final String dotpath="dotpath";
	
	private Text text;
	protected Object result;

	protected Shell shell;

	/**
	 * Create the dialog
	 * @param parent
	 * @param style
	 */
	public PreferencesDialog(Shell parent, int style) {
		super(parent, style);
	}

	/**
	 * Create the dialog
	 * @param parent
	 */
	public PreferencesDialog(Shell parent) {
		this(parent, SWT.NONE);
	}

	/**
	 * Open the dialog
	 * @return the result
	 */
	public Object open() {
		createContents();
		shell.open();
		shell.layout();
		final Display display = getParent().getDisplay();
		while (!shell.isDisposed()) {
			if (!display.readAndDispatch()) {
				display.sleep();
			}
		}
		return result;
	}

	/**
	 * Create contents of the dialog
	 */
	protected void createContents() {
		final Preferences my=Preferences.userRoot().node(GuiController.PLUGIN_ID);
		
		shell = new Shell(getParent(), SWT.DIALOG_TRIM | SWT.APPLICATION_MODAL);
		final GridLayout gridLayout_1 = new GridLayout();
		gridLayout_1.numColumns = 2;
		shell.setLayout(gridLayout_1);
		shell.setSize(500, 375);
		shell.setText("Preferences");

		final Group dottyGroup = new Group(shell, SWT.NONE);
		dottyGroup.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true, 2, 1));
		final GridLayout gridLayout = new GridLayout();
		gridLayout.numColumns = 2;
		dottyGroup.setLayout(gridLayout);
		dottyGroup.setText("Prefs");

		final Label chooseThePathLabel = new Label(dottyGroup, SWT.NONE);
		chooseThePathLabel.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, false, false, 2, 1));
		chooseThePathLabel.setText("choose the path of your DOT executable");

		text = new Text(dottyGroup, SWT.BORDER);
		text.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		text.setText(my.get(dotpath, ""));
		
		final Button chooseButton = new Button(dottyGroup, SWT.NONE);
		chooseButton.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(final SelectionEvent e) {
				final FileDialog fd= new FileDialog(shell, SWT.OPEN);
				fd.setText("Where is your DOT (not dotty!)");
				final String dotfile = fd.open();
				if(dotfile != null) {
					text.setText(dotfile);
				}
			}
		});
		chooseButton.setText("choose");

		final Button okButton = new Button(shell, SWT.NONE);
		okButton.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(final SelectionEvent e) {
				save();
				shell.dispose();
			}
		});
		final GridData gridData = new GridData(SWT.RIGHT, SWT.CENTER, true, false);
		gridData.minimumWidth = 80;
		okButton.setLayoutData(gridData);
		okButton.setText("OK");

		final Button cancelButton = new Button(shell, SWT.NONE);
		cancelButton.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(final SelectionEvent e) {
				shell.dispose();
			}
		});
		final GridData gridData_1 = new GridData(SWT.RIGHT, SWT.CENTER, false, false);
		gridData_1.widthHint = 80;
		cancelButton.setLayoutData(gridData_1);
		cancelButton.setText("Cancel");
		//
	}
	
	
	private void save(){
		final Preferences my=Preferences.userRoot().node(GuiController.PLUGIN_ID);
		my.put(dotpath, text.getText() );
		
		
	}

}
