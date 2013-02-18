package local.stalin.plugins.output.prefusevisualization.gui;

import java.util.ArrayList;
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

/**
 * Used to determine which model should be used (for simplicity we should
 * generlize inherit those chosing dialogs
 * 
 * @author keil
 * @version 0.0.1 
 * $LastChangedDate: 2008-03-16 12:54:00 +0100 (So, 16. Mär 2008) $
 * $LastChangedBy: keilr $
 * $LastChangedRevision: 501 $
 */
public class DisplayChooseDialog extends Dialog {

	private Combo combo;
	protected ArrayList<String> result;
	private final ArrayList<String> items;
	private final String dialogName;
	protected Shell shell;

	/**
	 * Create the dialog
	 * 
	 * @param parent
	 * @param style
	 */
	public DisplayChooseDialog(Shell parent, int style,
			ArrayList<String> items, String title) {
		super(parent, style);
		this.items = items;
		this.dialogName = title;
		result = new ArrayList<String>();
	}

	/**
	 * Create the dialog
	 * 
	 * @param parent
	 */
	public DisplayChooseDialog(Shell parent, ArrayList<String> items,
			String title) {
		this(parent, SWT.NONE, items, title);
	}

	/**
	 * Open the dialog
	 * 
	 * @return the result
	 */
	public ArrayList<String> open() {
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
		shell = new Shell(getParent(), SWT.DIALOG_TRIM | SWT.APPLICATION_MODAL);
		final GridLayout gridLayout = new GridLayout();
		gridLayout.numColumns = 2;
		shell.setLayout(gridLayout);
		shell.setSize(250, 200);
		shell.setText(dialogName);

		combo = new Combo(shell, SWT.READ_ONLY | SWT.SIMPLE);
		combo.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(final SelectionEvent e) {

				int i = combo.getSelectionIndex();
				if (i != -1) {
					String key = combo.getItem(i);
					if (key != null && !result.contains(key))
						result.add(key);
				}
			}
		});
		combo.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true, 2, 1));
		for (String item : items) {
			combo.add(item);
		}

		final Button okButton = new Button(shell, SWT.NONE);
		okButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(final SelectionEvent e) {
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
			public void widgetSelected(final SelectionEvent e) {
				result = new ArrayList<String>();
				shell.dispose();
			}
		});
		final GridData gridData = new GridData(80, SWT.DEFAULT);
		cancelButton.setLayoutData(gridData);
		cancelButton.setText("Cancel");
	}
}