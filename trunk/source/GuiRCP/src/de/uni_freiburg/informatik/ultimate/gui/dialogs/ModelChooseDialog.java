/*
 * Copyright (C) 2008-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 Jürgen Christ (christj@informatik.uni-freiburg.de)
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.MouseAdapter;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Dialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;

/**
 * 
 * Used to determine which model should be used (for simplicity we should generlize inherit those chosing dialogs 
 * 
 * @author dietsch / ortolf 
 *
 */
public class ModelChooseDialog extends Dialog {

	private org.eclipse.swt.widgets.List list;

	protected List<String> result;

	private final List<String> items;

	private final String dialogName;

	protected Shell shell;

	/**
	 * Create the dialog
	 * @param parent
	 * @param style
	 */
	public ModelChooseDialog(Shell parent, int style, List<String> items,
			String title) {
		super(parent, style);
		this.items = items;
		dialogName = title;
		result = new ArrayList<String>();
	}

	/**
	 * Create the dialog
	 * @param parent
	 */
	public ModelChooseDialog(Shell parent, List<String> items, String title) {
		this(parent, SWT.NONE, items, title);
	}

	/**
	 * Open the dialog
	 * @return the result
	 */
	public List<String> open() {
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
		shell = new Shell(getParent(), SWT.DIALOG_TRIM | SWT.APPLICATION_MODAL | SWT.RESIZE);
		final GridLayout gridLayout = new GridLayout();
		gridLayout.numColumns = 2;
		shell.setLayout(gridLayout);
		shell.setSize(900, 200);
		shell.setText(dialogName);

		list = new org.eclipse.swt.widgets.List(shell, SWT.READ_ONLY | SWT.MULTI | SWT.V_SCROLL | SWT.H_SCROLL);
		list.addMouseListener(new MouseAdapter() {

			@Override
			public void mouseDoubleClick(MouseEvent e) {
				result = Arrays.asList(list.getSelection());
				shell.dispose();
			}
		});
//		combo.addSelectionListener(new SelectionAdapter() {
//			public void widgetSelected(final SelectionEvent e) {
//
//				int i = combo.getSelectionIndex();
//				if (i != -1) {
//					String key = combo.getItem(i);
//					//TODO Check why SWTselect is called 2 times for a single selection and how we could handle mutliple selections
//					if (key != null && !result.contains(key))
//						result.add(key);
//				}
//			}
//		});
		list.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true, 2, 1));
		for (final String item : items) {
			list.add(item);
		}

		final Button okButton = new Button(shell, SWT.NONE);
		okButton.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(final SelectionEvent e) {
				result = Arrays.asList(list.getSelection());
				shell.dispose();
			}
		});
		final GridData gridData_1 = new GridData(SWT.RIGHT, SWT.CENTER, true,
				false);
		gridData_1.widthHint = 80;
		okButton.setLayoutData(gridData_1);
		okButton.setText("Ok");

		final Button cancelButton = new Button(shell, SWT.NONE);
		cancelButton.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(final SelectionEvent e) {
				result = Collections.emptyList();
				shell.dispose();
			}
		});
		final GridData gridData = new GridData(80, SWT.DEFAULT);
		cancelButton.setLayoutData(gridData);
		cancelButton.setText("Cancel");
	}

}
