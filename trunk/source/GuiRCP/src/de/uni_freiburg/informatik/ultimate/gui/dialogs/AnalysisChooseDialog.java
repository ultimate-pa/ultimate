package de.uni_freiburg.informatik.ultimate.gui.dialogs;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import javax.xml.bind.JAXBException;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.Toolchain;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IUltimatePlugin;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;
import de.uni_freiburg.informatik.ultimate.gui.GuiController;
import de.uni_freiburg.informatik.ultimate.gui.interfaces.IPreferencesKeys;

import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyAdapter;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.MouseAdapter;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Dialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.ui.preferences.ScopedPreferenceStore;
import org.xml.sax.SAXException;

public class AnalysisChooseDialog extends Dialog {

	private Table resulttable;
	private Table table;
	protected ArrayList<ITool> result = null;
	protected String toolchain_file = null;
	
	protected Shell shell;
	
	protected final List<ITool> tools,previous;

	/**
	 * Create the dialog
	 * @param parent
	 * @param style
	 */
	public AnalysisChooseDialog(Shell parent, int style, List<ITool> tools,List<ITool> previous) {
		super(parent, style);
		this.tools=tools;
		this.previous = previous;
	}

	/**
	 * Create the dialog
	 * @param parent
	 */
	public AnalysisChooseDialog(Shell parent, List<ITool> tools,List<ITool> previous) {
		this(parent, SWT.NONE, tools,previous);
	}

	/**
	 * Open the dialog
	 * @return the result
	 * @throws JAXBException 
	 * @throws FileNotFoundException 
	 * @throws SAXException 
	 */
	public Toolchain open() throws FileNotFoundException, JAXBException, SAXException {
		Toolchain result_chain;
		createContents();
		shell.layout();
		shell.setSize(shell.computeSize(SWT.DEFAULT, SWT.DEFAULT));
		shell.open();
		Display display = getParent().getDisplay();
		while (!shell.isDisposed()) {
			if (!display.readAndDispatch())
				display.sleep();
		}
		
		if (toolchain_file != null) {
			result_chain = new Toolchain(toolchain_file);
		} else if (result != null) {
			// convert selection into a toolchain
			result_chain = new Toolchain();
			for (ITool t : result) {
				result_chain.addPlugin(t.getPluginID());
			}
		} else {
			result_chain = null;
		}
		
		return result_chain;
	}

	/**
	 * Create contents of the dialog
	 */
	protected void createContents() {
		shell = new Shell(getParent(), SWT.DIALOG_TRIM | SWT.APPLICATION_MODAL | SWT.RESIZE);
		final GridLayout gridLayout = new GridLayout();
		gridLayout.numColumns = 4;
		
		shell.setLayout(gridLayout);
//		shell.setSize(400, 400);
		shell.setText("ToolChain Dialog");

		table = new Table(shell, SWT.FULL_SELECTION | SWT.BORDER | SWT.HIDE_SELECTION);
		table.addMouseListener(new MouseAdapter() {
			public void mouseDoubleClick(final MouseEvent e) {
				moveItem(SWT.RIGHT);
			}
		});
		table.setToolTipText("Mark the plugins that should be executed");
		table.setLinesVisible(false);
		table.setHeaderVisible(true);
		table.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));


		final TableColumn newColumnTableColumn = new TableColumn(table, SWT.NONE);
		
		Collections.sort(tools,new Comparator<ITool>() {

			@Override
			public int compare(ITool o1, ITool o2) {
				return o1.getName().compareTo(o2.getName());
			}
			
		});
		
		for (IUltimatePlugin analysis : tools) {
			final TableItem analysisTableItem = new TableItem(table, SWT.BORDER);
			analysisTableItem.setData(analysis);
			setCaption(analysisTableItem);
		}
		newColumnTableColumn.pack();
		newColumnTableColumn.setText("Available Plugins");
		newColumnTableColumn.setResizable(true);
		table.pack();

		resulttable = new Table(shell, SWT.BORDER);
		resulttable.addMouseListener(new MouseAdapter() {
			public void mouseDoubleClick(final MouseEvent e) {
				moveItem(SWT.LEFT);
			}
		});
		//a listener that should provide keyboard shortcuts for fast reordering
		resulttable.addKeyListener(new KeyAdapter() {
			public void keyPressed(final KeyEvent e) {
				if(e.stateMask == SWT.SHIFT){
					switch(e.keyCode){
					case SWT.ARROW_UP:
						moveItem(SWT.UP);
						e.doit = false; /* prevent moving selection */
						break;
					case SWT.ARROW_DOWN:
						moveItem(SWT.DOWN);
						e.doit = false; /* prevent moving selection */
						break;
					}		
				}
			}
		});
		resulttable.setToolTipText("Current selected toolchain");
		resulttable.setLinesVisible(false);
		resulttable.setHeaderVisible(true);
		resulttable.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true, 3, 1));

		final TableColumn newColumnTableColumn_1 = new TableColumn(resulttable, SWT.NONE);
		newColumnTableColumn_1.setWidth(newColumnTableColumn.getWidth());
		newColumnTableColumn_1.setText("Current Toolchain");
		newColumnTableColumn_1.setResizable(true);
		
		for (IUltimatePlugin analysis : previous) {
			final TableItem analysisTableItem = new TableItem(resulttable, SWT.BORDER);
			analysisTableItem.setData(analysis);
			setCaption(analysisTableItem);
		}
		resulttable.pack();

		final Button addButton = new Button(shell, SWT.NONE);
		addButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(final SelectionEvent e) {
				moveItem(SWT.RIGHT);
			}
		});
		addButton.setText("Add >>");

		final Button removeButton = new Button(shell, SWT.NONE);
		removeButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(final SelectionEvent e) {
				moveItem(SWT.LEFT);
			}
		});
		removeButton.setText("<< Remove");

		final Button upbutton = new Button(shell, SWT.ARROW | SWT.UP);
		upbutton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(final SelectionEvent e) {
				moveItem(SWT.UP);
			}
		});
		upbutton.setLayoutData(new GridData());
		upbutton.setText("up");

		final Button downbutton = new Button(shell, SWT.ARROW | SWT.DOWN);
		downbutton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(final SelectionEvent e) {
				moveItem(SWT.DOWN);
			}
		});
		downbutton.setLayoutData(new GridData());
		downbutton.setText("down");
		

		final Button okButton = new Button(shell, SWT.NONE);
		//gets all items from the resulttable and puts them in the resultset ..
		okButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(final SelectionEvent e) {
				result = new ArrayList < ITool >();
				for (TableItem item : resulttable.getItems()) {
					result.add((ITool)item.getData());
				}
				if (result.isEmpty()) {
					result = null;
				} else {
					shell.dispose();
				}
			}
		});
		final GridData gridData = new GridData(SWT.RIGHT, SWT.CENTER, false, false);
		gridData.widthHint = 80;
		okButton.setLayoutData(gridData);
		okButton.setText("OK");
		
		final Button xmlButton = new Button(shell, SWT.NONE);
		xmlButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(final SelectionEvent e) {

				InstanceScope iscope = new InstanceScope();
		        ScopedPreferenceStore store = new ScopedPreferenceStore(iscope,GuiController.s_PLUGIN_ID);
		        IEclipsePreferences prefscope = iscope.getNode(GuiController.s_PLUGIN_ID);
		        String filterpath = prefscope.get(IPreferencesKeys.LASTTOOLCHAINPATH, null);
				
				String[] extensions = new String[1];
				extensions[0] = "*.xml";
				FileDialog fd = new FileDialog(shell, SWT.OPEN
						| SWT.MULTI);
				fd.setText("Choose XML Toolchain");
				fd.setFilterExtensions(extensions);
				fd.setFileName(filterpath);
				toolchain_file = fd.open();
				if (toolchain_file != null) {
					prefscope.put(IPreferencesKeys.LASTTOOLCHAINPATH, toolchain_file);
					try {
						store.save();
					} catch (IOException exc) {
						exc.printStackTrace();
					}
					shell.dispose();
				}
			}
		});
		final GridData gridData_2 = new GridData(SWT.CENTER, SWT.CENTER, false, false);
		gridData_2.widthHint = 120;
		xmlButton.setLayoutData(gridData_2);
		xmlButton.setText("XML Toolchain");

		final Button cancelButton = new Button(shell, SWT.NONE);
		cancelButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(final SelectionEvent e) {
				shell.dispose();
			}
		});
		final GridData gridData_1 = new GridData(SWT.LEFT, SWT.CENTER, false, false, 2, 1);
		gridData_1.widthHint = 80;
		cancelButton.setLayoutData(gridData_1);
		cancelButton.setText("Cancel");
	}
	
	
	/**
	 * function for the listeners... will move the items appropriate
	 * @param swtDirection the SWT.Direction constant
	 * SWT.UP will move an item up in the resulttable
	 * SWT.DOWN will move an item down in the resulttable
	 * SWT.LEFT  will remove an item from the resulttable
	 * SWT.RIGHT will add an item to the resulttable
	 */
	private void moveItem(int swtDirection){
		//get currently selected items
		int ri = resulttable.getSelectionIndex();
		int li = table.getSelectionIndex();
		TableItem rightside  = null;
		TableItem leftside = null;
		if (ri != -1) {
			rightside = resulttable.getItem(ri);
		}
		if (li != -1) {
			leftside = table.getItem(li);
		}
		
		//make an action according to provided direction
		switch (swtDirection) {
		case SWT.LEFT:
			if (ri!= -1) {
				resulttable.getItem(ri).dispose();
			}
			break;
		case SWT.RIGHT:
			if (li != -1) {
				final TableItem ti = new TableItem(resulttable,SWT.NONE);
				ti.setData(leftside.getData());
				setCaption(ti);
			}
			break;
		case SWT.UP:
		case SWT.DOWN:
			if(rightside != null){
				//compute with which item we should switch
				int otherindex= ri + (swtDirection == SWT.UP? -1 : +1);
				if(ri != -1 && otherindex >= 0 && otherindex < resulttable.getItemCount()){
					TableItem oldItem = resulttable.getItem(ri);
					Object data = oldItem.getData();
					oldItem.dispose();
					TableItem newItem = new TableItem(resulttable, SWT.NONE, otherindex);
					newItem.setData(data);
					setCaption(newItem);
					resulttable.select(otherindex);
				}
				
			}
			
		}
		
//		table.getColumn(0).pack();
//		resulttable.getColumn(0).pack();
	}
	
	private static void setCaption(TableItem item){
		IUltimatePlugin isp = (IUltimatePlugin)item.getData();
		item.setText(isp.getName()+"   id: "+isp.getPluginID());
	}
	
}
