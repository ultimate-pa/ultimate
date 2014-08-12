package de.uni_freiburg.informatik.ultimate.gui.dialogs;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import javax.xml.bind.JAXBException;

import org.apache.log4j.Logger;
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
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IToolchainPlugin;
import de.uni_freiburg.informatik.ultimate.gui.GuiController;
import de.uni_freiburg.informatik.ultimate.gui.interfaces.IPreferencesKeys;

public class AnalysisChooseDialog extends Dialog {

	private Table mRresultTable;
	private Table mTable;
	private ArrayList<ITool> mResult;
	private String mToolchainFile;

	private Shell mShell;

	private final List<ITool> mTools;
	private final List<ITool> mPrevious;
	private final Logger mLogger;

	/**
	 * Create the dialog
	 * 
	 * @param parent
	 * @param style
	 */
	public AnalysisChooseDialog(Logger logger, Shell parent, int style, List<ITool> tools, List<ITool> previous) {
		super(parent, style);
		mTools = tools;
		mPrevious = previous;
		mLogger = logger;
		mToolchainFile = null;
		mResult = null;
	}

	/**
	 * Create the dialog
	 * 
	 * @param parent
	 */
	public AnalysisChooseDialog(Logger logger, Shell parent, List<ITool> tools, List<ITool> previous) {
		this(logger, parent, SWT.NONE, tools, previous);
	}

	/**
	 * Open the dialog
	 * 
	 * @return the result
	 * @throws JAXBException
	 * @throws FileNotFoundException
	 * @throws SAXException
	 */
	public ToolchainData open() throws FileNotFoundException, JAXBException, SAXException {
		ToolchainData result_chain;
		createContents();
		mShell.layout();
		mShell.setSize(mShell.computeSize(SWT.DEFAULT, SWT.DEFAULT));
		mShell.open();
		Display display = getParent().getDisplay();
		while (!mShell.isDisposed()) {
			if (!display.readAndDispatch())
				display.sleep();
		}

		if (mToolchainFile != null) {
			mLogger.info("Reading toolchain file from " + mToolchainFile);
			result_chain = new ToolchainData(mToolchainFile);
		} else if (mResult != null) {
			// convert selection into a toolchain
			result_chain = new ToolchainData();
			for (ITool t : mResult) {
				result_chain.addPlugin(t.getPluginID());
			}
			//save this toolchain in a tempfile for redo actions 
			String tDir = System.getProperty("java.io.tmpdir");
			File tmpToolchain = new File(tDir, "lastUltimateToolchain.xml");
			result_chain.writeToFile(tmpToolchain.getAbsolutePath());
			new UltimatePreferenceStore(GuiController.sPLUGINID).put(IPreferencesKeys.LASTTOOLCHAINPATH,
					tmpToolchain.getAbsolutePath());
			mLogger.info("Saved custom toolchain to " + tmpToolchain.getAbsolutePath());

		} else {
			result_chain = null;
		}

		return result_chain;
	}

	/**
	 * Create contents of the dialog
	 */
	protected void createContents() {
		mShell = new Shell(getParent(), SWT.DIALOG_TRIM | SWT.APPLICATION_MODAL | SWT.RESIZE);
		final GridLayout gridLayout = new GridLayout();
		gridLayout.numColumns = 4;

		mShell.setLayout(gridLayout);
		// shell.setSize(400, 400);
		mShell.setText("ToolChain Dialog");

		mTable = new Table(mShell, SWT.FULL_SELECTION | SWT.BORDER | SWT.HIDE_SELECTION);
		mTable.addMouseListener(new MouseAdapter() {
			public void mouseDoubleClick(final MouseEvent e) {
				moveItem(SWT.RIGHT);
			}
		});
		mTable.setToolTipText("Mark the plugins that should be executed");
		mTable.setLinesVisible(false);
		mTable.setHeaderVisible(true);
		mTable.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));

		final TableColumn newColumnTableColumn = new TableColumn(mTable, SWT.NONE);

		Collections.sort(mTools, new Comparator<ITool>() {

			@Override
			public int compare(ITool o1, ITool o2) {
				return o1.getPluginName().compareTo(o2.getPluginName());
			}

		});

		for (IToolchainPlugin analysis : mTools) {
			final TableItem analysisTableItem = new TableItem(mTable, SWT.BORDER);
			analysisTableItem.setData(analysis);
			setCaption(analysisTableItem);
		}
		newColumnTableColumn.pack();
		newColumnTableColumn.setText("Available Plugins");
		newColumnTableColumn.setResizable(true);
		mTable.pack();

		mRresultTable = new Table(mShell, SWT.BORDER);
		mRresultTable.addMouseListener(new MouseAdapter() {
			public void mouseDoubleClick(final MouseEvent e) {
				moveItem(SWT.LEFT);
			}
		});
		// a listener that should provide keyboard shortcuts for fast reordering
		mRresultTable.addKeyListener(new KeyAdapter() {
			public void keyPressed(final KeyEvent e) {
				if (e.stateMask == SWT.SHIFT) {
					switch (e.keyCode) {
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
		mRresultTable.setToolTipText("Current selected toolchain");
		mRresultTable.setLinesVisible(false);
		mRresultTable.setHeaderVisible(true);
		mRresultTable.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true, 3, 1));

		final TableColumn newColumnTableColumn_1 = new TableColumn(mRresultTable, SWT.NONE);
		newColumnTableColumn_1.setWidth(newColumnTableColumn.getWidth());
		newColumnTableColumn_1.setText("Current Toolchain");
		newColumnTableColumn_1.setResizable(true);

		for (IToolchainPlugin analysis : mPrevious) {
			final TableItem analysisTableItem = new TableItem(mRresultTable, SWT.BORDER);
			analysisTableItem.setData(analysis);
			setCaption(analysisTableItem);
		}
		mRresultTable.pack();

		final Button addButton = new Button(mShell, SWT.NONE);
		addButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(final SelectionEvent e) {
				moveItem(SWT.RIGHT);
			}
		});
		addButton.setText("Add >>");

		final Button removeButton = new Button(mShell, SWT.NONE);
		removeButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(final SelectionEvent e) {
				moveItem(SWT.LEFT);
			}
		});
		removeButton.setText("<< Remove");

		final Button upbutton = new Button(mShell, SWT.ARROW | SWT.UP);
		upbutton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(final SelectionEvent e) {
				moveItem(SWT.UP);
			}
		});
		upbutton.setLayoutData(new GridData());
		upbutton.setText("up");

		final Button downbutton = new Button(mShell, SWT.ARROW | SWT.DOWN);
		downbutton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(final SelectionEvent e) {
				moveItem(SWT.DOWN);
			}
		});
		downbutton.setLayoutData(new GridData());
		downbutton.setText("down");

		final Button okButton = new Button(mShell, SWT.NONE);
		// gets all items from the resulttable and puts them in the resultset ..
		okButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(final SelectionEvent e) {
				mResult = new ArrayList<ITool>();
				for (TableItem item : mRresultTable.getItems()) {
					mResult.add((ITool) item.getData());
				}
				if (mResult.isEmpty()) {
					mResult = null;
				} else {
					mShell.dispose();
				}
			}
		});
		final GridData gridData = new GridData(SWT.RIGHT, SWT.CENTER, false, false);
		gridData.widthHint = 80;
		okButton.setLayoutData(gridData);
		okButton.setText("OK");

		final Button xmlButton = new Button(mShell, SWT.NONE);
		xmlButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(final SelectionEvent e) {

				UltimatePreferenceStore prefs = new UltimatePreferenceStore(GuiController.sPLUGINID);
				String filterpath = prefs.getString(IPreferencesKeys.LASTTOOLCHAINPATH, null);

				String[] extensions = new String[1];
				extensions[0] = "*.xml";
				FileDialog fd = new FileDialog(mShell, SWT.OPEN | SWT.MULTI);
				fd.setText("Choose XML Toolchain");
				fd.setFilterExtensions(extensions);
				fd.setFileName(filterpath);
				mToolchainFile = fd.open();
				if (mToolchainFile != null) {
					prefs.put(IPreferencesKeys.LASTTOOLCHAINPATH, mToolchainFile);
					mShell.dispose();
				}
			}
		});
		final GridData gridData_2 = new GridData(SWT.CENTER, SWT.CENTER, false, false);
		gridData_2.widthHint = 120;
		xmlButton.setLayoutData(gridData_2);
		xmlButton.setText("XML Toolchain");

		final Button cancelButton = new Button(mShell, SWT.NONE);
		cancelButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(final SelectionEvent e) {
				mShell.dispose();
			}
		});
		final GridData gridData_1 = new GridData(SWT.LEFT, SWT.CENTER, false, false, 2, 1);
		gridData_1.widthHint = 80;
		cancelButton.setLayoutData(gridData_1);
		cancelButton.setText("Cancel");
	}

	/**
	 * function for the listeners... will move the items appropriate
	 * 
	 * @param swtDirection
	 *            the SWT.Direction constant SWT.UP will move an item up in the
	 *            resulttable SWT.DOWN will move an item down in the resulttable
	 *            SWT.LEFT will remove an item from the resulttable SWT.RIGHT
	 *            will add an item to the resulttable
	 */
	private void moveItem(int swtDirection) {
		// get currently selected items
		int ri = mRresultTable.getSelectionIndex();
		int li = mTable.getSelectionIndex();
		TableItem rightside = null;
		TableItem leftside = null;
		if (ri != -1) {
			rightside = mRresultTable.getItem(ri);
		}
		if (li != -1) {
			leftside = mTable.getItem(li);
		}

		// make an action according to provided direction
		switch (swtDirection) {
		case SWT.LEFT:
			if (ri != -1) {
				mRresultTable.getItem(ri).dispose();
			}
			break;
		case SWT.RIGHT:
			if (li != -1) {
				final TableItem ti = new TableItem(mRresultTable, SWT.NONE);
				ti.setData(leftside.getData());
				setCaption(ti);
			}
			break;
		case SWT.UP:
		case SWT.DOWN:
			if (rightside != null) {
				// compute with which item we should switch
				int otherindex = ri + (swtDirection == SWT.UP ? -1 : +1);
				if (ri != -1 && otherindex >= 0 && otherindex < mRresultTable.getItemCount()) {
					TableItem oldItem = mRresultTable.getItem(ri);
					Object data = oldItem.getData();
					oldItem.dispose();
					TableItem newItem = new TableItem(mRresultTable, SWT.NONE, otherindex);
					newItem.setData(data);
					setCaption(newItem);
					mRresultTable.select(otherindex);
				}

			}

		}

		// table.getColumn(0).pack();
		// resulttable.getColumn(0).pack();
	}

	private static void setCaption(TableItem item) {
		IToolchainPlugin isp = (IToolchainPlugin) item.getData();
		item.setText(isp.getPluginName() + "   id: " + isp.getPluginID());
	}

}
