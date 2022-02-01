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
import org.eclipse.swt.events.SelectionListener;
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

	private Table mSelectedToolsTable;
	private Table mAvailableToolsTable;
	private List<ITool> mResult;
	private String mToolchainFilePath;
	private Shell mShell;

	private final List<ITool> mAvailableTools;
	private final List<ITool> mPreviouslySelectedTools;
	private final ILogger mLogger;
	private final ICore<RunDefinition> mCore;

	public AnalysisChooseDialog(final ILogger logger, final Shell parent, final List<ITool> tools,
			final List<ITool> previous, final ICore<RunDefinition> core) {
		super(parent, SWT.NONE);
		mAvailableTools = tools;
		mPreviouslySelectedTools = previous;
		mLogger = logger;
		mCore = core;
		mToolchainFilePath = null;
		mResult = null;
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
		if (mToolchainFilePath != null) {
			mLogger.info("Reading toolchain file from " + mToolchainFilePath);
			resultChain = mCore.createToolchainData(mToolchainFilePath);
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
					resultChain.getRootElement().getToolchain());
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
		mShell = new Shell(SWT.DIALOG_TRIM | SWT.APPLICATION_MODAL | SWT.RESIZE);
		final GridLayout gridLayout = new GridLayout();
		gridLayout.numColumns = 4;

		mShell.setLayout(gridLayout);
		mShell.setText("Toolchain Dialog");

		final TableColumn newColumnTableColumn = createContentsAvailableToolsTable();
		createContentsSelectedToolsTable(newColumnTableColumn.getWidth());

		addButton("Add >>", SWT.NONE, new ItemMoveSelectionAdapter(SWT.RIGHT));
		addButton("<< Remove", SWT.NONE, new ItemMoveSelectionAdapter(SWT.LEFT));
		addButton("up", SWT.ARROW | SWT.UP, new ItemMoveSelectionAdapter(SWT.UP));
		addButton("down", SWT.ARROW | SWT.DOWN, new ItemMoveSelectionAdapter(SWT.DOWN));

		final GridData gridDataOkButton = new GridData(SWT.RIGHT, SWT.CENTER, false, false);
		gridDataOkButton.widthHint = 80;
		addButton("OK", SWT.NONE, new ResultSelectionAdapter(), gridDataOkButton);

		final GridData gridDataXmlButton = new GridData(SWT.CENTER, SWT.CENTER, false, false);
		gridDataXmlButton.widthHint = 120;
		addButton("XML Toolchain", SWT.NONE, new LoadFromXMLFileSelectionAdapter(), gridDataXmlButton);

		final GridData gridDataCancelButton = new GridData(SWT.LEFT, SWT.CENTER, false, false, 2, 1);
		gridDataCancelButton.widthHint = 80;
		addButton("Cancel", SWT.NONE, new CloseShellSelectionAdapter(), gridDataCancelButton);
	}

	private Button addButton(final String label, final int buttonStyle, final SelectionListener selectionAdapter) {
		return addButton(label, buttonStyle, selectionAdapter, new GridData());
	}

	private Button addButton(final String label, final int buttonStyle, final SelectionListener selectionAdapter,
			final Object layoutData) {
		final Button addButton = new Button(mShell, buttonStyle);
		addButton.addSelectionListener(selectionAdapter);
		addButton.setText(label);
		addButton.setLayoutData(layoutData);
		return addButton;
	}

	private void createContentsSelectedToolsTable(final int width) {
		mSelectedToolsTable = new Table(mShell, SWT.BORDER);
		mSelectedToolsTable.addMouseListener(new MouseAdapter() {
			@Override
			public void mouseDoubleClick(final MouseEvent e) {
				moveItem(SWT.LEFT);
			}
		});
		// a listener that should provide keyboard shortcuts for fast reordering
		mSelectedToolsTable.addKeyListener(new KeyAdapter() {
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
					default:
						break;
					}
				}
			}
		});
		mSelectedToolsTable.setToolTipText("Current selected toolchain");
		mSelectedToolsTable.setLinesVisible(false);
		mSelectedToolsTable.setHeaderVisible(true);
		mSelectedToolsTable.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true, 3, 1));

		final TableColumn tableColumn = new TableColumn(mSelectedToolsTable, SWT.NONE);
		tableColumn.setWidth(width);
		tableColumn.setText("Current Toolchain");
		tableColumn.setResizable(true);

		for (final IToolchainPlugin analysis : mPreviouslySelectedTools) {
			final TableItem analysisTableItem = new TableItem(mSelectedToolsTable, SWT.BORDER);
			analysisTableItem.setData(analysis);
			setCaption(analysisTableItem);
		}
		mSelectedToolsTable.pack();
	}

	private TableColumn createContentsAvailableToolsTable() {
		mAvailableToolsTable = new Table(mShell, SWT.FULL_SELECTION | SWT.BORDER | SWT.HIDE_SELECTION);
		mAvailableToolsTable.addMouseListener(new MouseAdapter() {
			@Override
			public void mouseDoubleClick(final MouseEvent e) {
				moveItem(SWT.RIGHT);
			}
		});
		mAvailableToolsTable.setToolTipText("Mark the plugins that should be executed");
		mAvailableToolsTable.setLinesVisible(false);
		mAvailableToolsTable.setHeaderVisible(true);
		mAvailableToolsTable.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));

		final TableColumn tableColumn = new TableColumn(mAvailableToolsTable, SWT.NONE);

		Collections.sort(mAvailableTools, new Comparator<ITool>() {

			@Override
			public int compare(final ITool o1, final ITool o2) {
				return o1.getPluginName().compareTo(o2.getPluginName());
			}

		});

		for (final IToolchainPlugin analysis : mAvailableTools) {
			final TableItem availableToolsTableItem = new TableItem(mAvailableToolsTable, SWT.BORDER);
			availableToolsTableItem.setData(analysis);
			setCaption(availableToolsTableItem);
		}
		tableColumn.pack();
		tableColumn.setText("Available Plugins");
		tableColumn.setResizable(true);
		mAvailableToolsTable.pack();
		return tableColumn;
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
		final int rItemIdx = mSelectedToolsTable.getSelectionIndex();
		final int lItemIdx = mAvailableToolsTable.getSelectionIndex();
		final TableItem rightItem = rItemIdx == -1 ? null : mSelectedToolsTable.getItem(rItemIdx);
		final TableItem leftItem = lItemIdx == -1 ? null : mAvailableToolsTable.getItem(lItemIdx);

		if (rightItem == null && leftItem == null) {
			return;
		}

		if (swtDirection == SWT.LEFT && rightItem != null) {
			mSelectedToolsTable.getItem(rItemIdx).dispose();
			return;
		}

		if (swtDirection == SWT.RIGHT && leftItem != null) {
			final TableItem ti = new TableItem(mSelectedToolsTable, SWT.NONE);
			ti.setData(leftItem.getData());
			setCaption(ti);
			return;
		}

		if ((swtDirection == SWT.UP || swtDirection == SWT.DOWN) && rightItem != null) {
			// compute with which item we should switch
			final int otherindex = rItemIdx + (swtDirection == SWT.UP ? -1 : +1);
			if (rItemIdx == -1 || otherindex < 0 || otherindex >= mSelectedToolsTable.getItemCount()) {
				// we are the only item or we cannot move
				return;
			}
			final TableItem oldItem = mSelectedToolsTable.getItem(rItemIdx);
			final Object data = oldItem.getData();
			oldItem.dispose();
			final TableItem newItem = new TableItem(mSelectedToolsTable, SWT.NONE, otherindex);
			newItem.setData(data);
			setCaption(newItem);
			mSelectedToolsTable.select(otherindex);
			return;
		}
	}

	private static void setCaption(final TableItem item) {
		final IToolchainPlugin isp = (IToolchainPlugin) item.getData();
		item.setText(isp.getPluginName() + "   id: " + isp.getPluginID());
	}

	private final class CloseShellSelectionAdapter extends SelectionAdapter {
		@Override
		public void widgetSelected(final SelectionEvent e) {
			mShell.dispose();
		}
	}

	private final class LoadFromXMLFileSelectionAdapter extends SelectionAdapter {
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
			mToolchainFilePath = fd.open();
			if (mToolchainFilePath != null) {
				prefs.put(IPreferencesKeys.LASTTOOLCHAINPATH, mToolchainFilePath);
				mShell.dispose();
			}
		}
	}

	private final class ItemMoveSelectionAdapter extends SelectionAdapter {

		private final int mMoveItemDirection;

		private ItemMoveSelectionAdapter(final int moveItemDirection) {
			mMoveItemDirection = moveItemDirection;
		}

		@Override
		public void widgetSelected(final SelectionEvent e) {
			moveItem(mMoveItemDirection);
		}
	}

	private final class ResultSelectionAdapter extends SelectionAdapter {
		@Override
		public void widgetSelected(final SelectionEvent e) {
			mResult = new ArrayList<>();
			for (final TableItem item : mSelectedToolsTable.getItems()) {
				mResult.add((ITool) item.getData());
			}
			if (mResult.isEmpty()) {
				mResult = null;
			} else {
				mShell.dispose();
			}
		}
	}
}
