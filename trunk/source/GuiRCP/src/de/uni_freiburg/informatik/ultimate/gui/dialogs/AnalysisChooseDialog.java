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

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import javax.xml.bind.JAXBException;

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

import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.ToolchainFileValidator;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.ITool;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainPlugin;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.gui.GuiController;
import de.uni_freiburg.informatik.ultimate.gui.interfaces.IPreferencesKeys;

/**
 *
 * @author Jürgen Christ
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class AnalysisChooseDialog extends Dialog {

	private Table mRresultTable;
	private Table mTable;
	private List<ITool> mResult;
	private String mToolchainFile;
	private Shell mShell;

	private final List<ITool> mTools;
	private final List<ITool> mPrevious;
	private final ILogger mLogger;
	private final ICore<RunDefinition> mCore;

	public AnalysisChooseDialog(final ILogger logger, final Shell parent, final int style, final List<ITool> tools,
			final List<ITool> previous, final ICore<RunDefinition> core) {
		super(parent, style);
		mTools = tools;
		mPrevious = previous;
		mLogger = logger;
		mCore = core;
		mToolchainFile = null;
		mResult = null;
	}

	public AnalysisChooseDialog(final ILogger logger, final Shell parent, final List<ITool> tools,
			final List<ITool> previous, final ICore<RunDefinition> core) {
		this(logger, parent, SWT.NONE, tools, previous, core);
	}

	public IToolchainData<RunDefinition> open() throws FileNotFoundException, JAXBException, SAXException {
		createContents();
		mShell.layout();
		mShell.setSize(mShell.computeSize(SWT.DEFAULT, SWT.DEFAULT));
		mShell.open();
		final Display display = getParent().getDisplay();
		while (!mShell.isDisposed()) {
			if (!display.readAndDispatch()) {
				display.sleep();
			}
		}

		final IToolchainData<RunDefinition> resultChain;
		if (mToolchainFile != null) {
			mLogger.info("Reading toolchain file from " + mToolchainFile);
			resultChain = mCore.createToolchainData(mToolchainFile);
		} else if (mResult != null) {
			// convert selection into a toolchain
			resultChain = mCore.createToolchainData();
			for (final ITool t : mResult) {
				resultChain.addPlugin(t.getPluginID());
			}
			// save this toolchain in a tempfile for redo actions
			final String tDir = System.getProperty("java.io.tmpdir");
			final File tmpToolchain = new File(tDir, "lastUltimateToolchain.xml");
			new ToolchainFileValidator().saveToolchain(tmpToolchain.getAbsolutePath(), "Last Ultimate Toolchain",
					resultChain.getToolchain().getToolchain());
			mCore.getPreferenceProvider(GuiController.PLUGIN_ID).put(IPreferencesKeys.LASTTOOLCHAINPATH,
					tmpToolchain.getAbsolutePath());
			mLogger.info("Saved custom toolchain to " + tmpToolchain.getAbsolutePath());

		} else {
			resultChain = null;
		}

		return resultChain;
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
			@Override
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
			public int compare(final ITool o1, final ITool o2) {
				return o1.getPluginName().compareTo(o2.getPluginName());
			}

		});

		for (final IToolchainPlugin analysis : mTools) {
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
			@Override
			public void mouseDoubleClick(final MouseEvent e) {
				moveItem(SWT.LEFT);
			}
		});
		// a listener that should provide keyboard shortcuts for fast reordering
		mRresultTable.addKeyListener(new KeyAdapter() {
			@Override
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

		for (final IToolchainPlugin analysis : mPrevious) {
			final TableItem analysisTableItem = new TableItem(mRresultTable, SWT.BORDER);
			analysisTableItem.setData(analysis);
			setCaption(analysisTableItem);
		}
		mRresultTable.pack();

		final Button addButton = new Button(mShell, SWT.NONE);
		addButton.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(final SelectionEvent e) {
				moveItem(SWT.RIGHT);
			}
		});
		addButton.setText("Add >>");

		final Button removeButton = new Button(mShell, SWT.NONE);
		removeButton.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(final SelectionEvent e) {
				moveItem(SWT.LEFT);
			}
		});
		removeButton.setText("<< Remove");

		final Button upbutton = new Button(mShell, SWT.ARROW | SWT.UP);
		upbutton.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(final SelectionEvent e) {
				moveItem(SWT.UP);
			}
		});
		upbutton.setLayoutData(new GridData());
		upbutton.setText("up");

		final Button downbutton = new Button(mShell, SWT.ARROW | SWT.DOWN);
		downbutton.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(final SelectionEvent e) {
				moveItem(SWT.DOWN);
			}
		});
		downbutton.setLayoutData(new GridData());
		downbutton.setText("down");

		final Button okButton = new Button(mShell, SWT.NONE);
		// gets all items from the resulttable and puts them in the resultset ..
		okButton.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(final SelectionEvent e) {
				mResult = new ArrayList<ITool>();
				for (final TableItem item : mRresultTable.getItems()) {
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
			@Override
			public void widgetSelected(final SelectionEvent e) {

				final IPreferenceProvider prefs = mCore.getPreferenceProvider(GuiController.PLUGIN_ID);
				final String filterpath = prefs.getString(IPreferencesKeys.LASTTOOLCHAINPATH, null);

				final String[] extensions = new String[1];
				extensions[0] = "*.xml";
				final FileDialog fd = new FileDialog(mShell, SWT.OPEN | SWT.MULTI);
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
			@Override
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
	 *            the SWT.Direction constant SWT.UP will move an item up in the resulttable SWT.DOWN will move an item
	 *            down in the resulttable SWT.LEFT will remove an item from the resulttable SWT.RIGHT will add an item
	 *            to the resulttable
	 */
	private void moveItem(final int swtDirection) {
		// get currently selected items
		final int ri = mRresultTable.getSelectionIndex();
		final int li = mTable.getSelectionIndex();
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
				final int otherindex = ri + (swtDirection == SWT.UP ? -1 : +1);
				if (ri != -1 && otherindex >= 0 && otherindex < mRresultTable.getItemCount()) {
					final TableItem oldItem = mRresultTable.getItem(ri);
					final Object data = oldItem.getData();
					oldItem.dispose();
					final TableItem newItem = new TableItem(mRresultTable, SWT.NONE, otherindex);
					newItem.setData(data);
					setCaption(newItem);
					mRresultTable.select(otherindex);
				}

			}

		}

		// table.getColumn(0).pack();
		// resulttable.getColumn(0).pack();
	}

	private static void setCaption(final TableItem item) {
		final IToolchainPlugin isp = (IToolchainPlugin) item.getData();
		item.setText(isp.getPluginName() + "   id: " + isp.getPluginID());
	}

}
