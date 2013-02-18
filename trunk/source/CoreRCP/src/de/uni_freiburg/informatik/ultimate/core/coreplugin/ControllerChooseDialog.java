package de.uni_freiburg.informatik.ultimate.core.coreplugin;


import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Shell;

/**
 * A quick-and-dirty implementation of a simple dialog
 * that takes a list of suitable controllers, presents
 * them in a list widget, and awaits a selection from
 * the user.
 * 
 * @author Christian Simon
 *
 */
public class ControllerChooseDialog {
	
	private int m_Result;
	private Display m_Display;
	private Shell m_Shell;
	private List m_List;
	private java.util.List<IConfigurationElement> m_Controllers;

	public ControllerChooseDialog (java.util.List<IConfigurationElement> suitableControllers) {
		m_Display = new Display();
		m_Shell = new Shell(m_Display);
		this.m_Controllers = suitableControllers;
		createContents();
		
	}
	
	private void createContents() {
		m_Shell.setText("Ultimate Controller Chooser");
		org.eclipse.swt.graphics.Rectangle bounds = m_Display.getBounds();
		m_Shell.setBounds((bounds.width - 500) / 2, (bounds.height - 400) / 2, 400, 200);
		GridLayout layout = new GridLayout(2, true);
		layout.numColumns = 2;
		m_Shell.setLayout(layout);
		
		final Label label = new Label(m_Shell, SWT.WRAP);
		
		label.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true, 2, 1));
		label.setText("More than 1 GUI controller was found. Please make a selection.");
		
		// we want a horizontal and vertical scroll bar for our list
		m_List = new List(m_Shell, SWT.SINGLE | SWT.V_SCROLL | SWT.H_SCROLL);
		
		m_List.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true, 2, 1));
		for (IConfigurationElement ce: this.m_Controllers) {
			m_List.add(ce.getAttribute("class"));
		}
		
		// we want a double-click to be 
		// equivalent to the okay button
		m_List.addMouseListener(new MouseListener() {

			@Override
			public void mouseDoubleClick(MouseEvent e) {
				m_Result = m_List.getSelectionIndex();
				m_Shell.dispose();
				m_Display.close();
			}

			@Override
			public void mouseDown(MouseEvent e) {				
			}

			@Override
			public void mouseUp(MouseEvent e) {
			}
			
		});
		
		final Button okButton = new Button(m_Shell, SWT.NONE);
		okButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(final SelectionEvent e) {
				m_Result = m_List.getSelectionIndex();
				m_Shell.dispose();
				m_Display.close();
			}
		});
		
		okButton.setLayoutData(new GridData(SWT.CENTER, SWT.CENTER, false, false));
		okButton.setText("OK");
		
		final Button cancelButton = new Button(m_Shell, SWT.NONE);
		cancelButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(final SelectionEvent e) {
				m_Result = -1;
				m_Shell.dispose();
				m_Display.close();
			}
		});
		cancelButton.setLayoutData(new GridData(SWT.CENTER, SWT.CENTER, false, false));
		cancelButton.setText("Quit");
	}
	
	/**
	 * 'Main' function that will be called from the process that wants this dialog
	 * (usually the Core). This will open the shell, wait for it to be closed and
	 * then return the result value.
	 * 
	 * @return integer >=0 of selected list index, -1 if no valid selection was made
	 */
	public int open() {
		m_Shell.open ();
		while (!m_Shell.isDisposed ()) {
				if (!m_Display.readAndDispatch ()) m_Display.sleep ();
		}		
		return m_Result;
	} 

}
