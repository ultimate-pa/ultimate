package de.uni_freiburg.informatik.ultimate.gui.dialogs;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Dialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;

public class ParserChooseDialog extends Dialog {

	private Combo combo;
	protected  ISource result;
	private final Collection<ISource> parsers;

	protected Shell shell;
	
	

	/**
	 * Create the dialog
	 * @param parent
	 * @param style
	 */
	public ParserChooseDialog(Shell parent, int style, Collection< ISource> parsers) {
		super(parent, style);
		this.parsers=parsers;
		
	}

	/**
	 * Create the dialog
	 * @param parent
	 */
	public ParserChooseDialog(Shell parent, Collection< ISource> parsers) {
		this(parent, SWT.NONE, parsers);
	}

	/**
	 * Open the dialog
	 * @return the result
	 */
	public  ISource open() {
		createContents();
		shell.open();
		shell.layout();
		Display display = getParent().getDisplay();
		while (!shell.isDisposed()) {
			if (!display.readAndDispatch())
				display.sleep();
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
		shell.setSize(250, 200);
		shell.setText("Choose a parser");

		combo = new Combo(shell, SWT.READ_ONLY | SWT.SIMPLE);
		combo.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(final SelectionEvent e) {
				int i = combo.getSelectionIndex();
				if (i != -1) {
				String key = combo.getItem(i);
				if (key != null)
					result = ( ISource ) combo.getData(key);
				}
			}
		});
		combo.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true, 2, 1));
		for ( ISource parser : parsers) {
			String key = parser.getPluginName();
			combo.add(key);
			combo.setData(key, parser);
		}
		
		
		
		final Button okButton = new Button(shell, SWT.NONE);
		okButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(final SelectionEvent e) {
				shell.dispose();
			}
		});
		final GridData gridData_1 = new GridData(SWT.RIGHT, SWT.CENTER, true, false);
		gridData_1.widthHint = 80;
		okButton.setLayoutData(gridData_1);
		okButton.setText("Ok");

		final Button cancelButton = new Button(shell, SWT.NONE);
		cancelButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(final SelectionEvent e) {
				result = null;
				shell.dispose();
			}
		});
		final GridData gridData = new GridData(80, SWT.DEFAULT);
		cancelButton.setLayoutData(gridData);
		cancelButton.setText("Cancel");
		//
	}

}
