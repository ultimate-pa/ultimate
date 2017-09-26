/*
 * Copyright (C) 2007-2015 Christian Ortolf
 * Copyright (C) 2007-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.gui;

import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import javax.xml.bind.JAXBException;

import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PlatformUI;
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultSummarizer;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.ITool;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchain;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILoggingService;
import de.uni_freiburg.informatik.ultimate.gui.advisors.ApplicationWorkbenchAdvisor;
import de.uni_freiburg.informatik.ultimate.gui.dialogs.AnalysisChooseDialog;
import de.uni_freiburg.informatik.ultimate.gui.dialogs.ModelChooseDialog;
import de.uni_freiburg.informatik.ultimate.gui.dialogs.ParserChooseDialog;

/**
 * GUIController is the IController<RunDefinition> implementation of the UltimateDebug GUI
 *
 * @author dietsch
 *
 */
public class GuiController implements IController<RunDefinition> {

	public static final String PLUGIN_ID = GuiController.class.getPackage().getName();
	public static final String PLUGIN_NAME = "Gui Controller";

	private ILogger mLogger;
	private Display mDisplay;

	private volatile ISource mParser;
	private volatile IToolchainData<RunDefinition> mTools;
	private volatile List<String> mModels;

	private ICore<RunDefinition> mCore;
	private TrayIconNotifier mTrayIconNotifier;
	private IToolchain<RunDefinition> mCurrentToolchain;
	private ILoggingService mLoggingService;

	/**
	 * Initialization of Controller. The GUI is created here. Note: This methods blocks until the GUI is closed.
	 *
	 * @return the exit code for the application
	 */
	@Override
	public int init(final ICore<RunDefinition> core) {
		if (core == null) {
			throw new IllegalArgumentException("core may not be null");
		}
		mLoggingService = core.getCoreLoggingService();
		mLogger = mLoggingService.getControllerLogger();
		mCore = core;
		mDisplay = PlatformUI.createDisplay();
		if (mDisplay == null) {
			mLogger.fatal("PlatformUI.createDisplay() delivered null-value, cannot create workbench, exiting...");
			return -1;
		}

		mParser = null;
		mModels = new ArrayList<>();
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Creating Workbench ...");
			mLogger.debug("--------------------------------------------------------------------------------");
		}
		int returnCode = -1;
		final ApplicationWorkbenchAdvisor workbenchAdvisor = new ApplicationWorkbenchAdvisor();
		mTrayIconNotifier = new TrayIconNotifier(workbenchAdvisor);
		workbenchAdvisor.init(mCore, mTrayIconNotifier, this, mLogger);
		try {
			returnCode = PlatformUI.createAndRunWorkbench(mDisplay, workbenchAdvisor);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("GUI return code: " + returnCode);
			}
			return returnCode;
		} catch (final Exception ex) {
			mLogger.fatal("An exception occured", ex);
			return returnCode;
		} finally {
			setAfterRerunCurrentToolchain(null);
			mDisplay.dispose();
		}
	}

	@Override
	public synchronized ISource selectParser(final Collection<ISource> parsers) {
		mDisplay.syncExec(() -> {
			final Shell shell = new Shell(mDisplay);
			mParser = new ParserChooseDialog(shell, parsers).open();
		});
		return mParser;
	}

	@Override
	public synchronized IToolchainData<RunDefinition> selectTools(final List<ITool> tools) {
		final List<ITool> previous = Collections.emptyList();
		return selectTools(tools, previous);
	}

	private synchronized IToolchainData<RunDefinition> selectTools(final List<ITool> tools,
			final List<ITool> previous) {
		mDisplay.syncExec(() -> {
			final Shell shell = new Shell(mDisplay);
			try {
				mTools = new AnalysisChooseDialog(mLogger, shell, tools, previous, mCore).open();
			} catch (final FileNotFoundException e1) {
				MessageDialog.openError(shell, "An error occured", "Toolchain XML file was not found.");

			} catch (final JAXBException e2) {
				MessageDialog.openError(shell, "An error occured", "Toolchain XML file could not be validated.");
			} catch (final SAXException e3) {
				MessageDialog.openError(shell, "An error occured", "Toolchain XML file could not be properly parsed.");
			}
		});
		return mTools;
	}

	@Override
	public synchronized List<String> selectModel(final List<String> modelNames) {
		mDisplay.syncExec(() -> {
			final Shell shell = new Shell(mDisplay);
			mModels = new ModelChooseDialog(shell, modelNames, "Choose the model").open();
		});
		return mModels;
	}

	@Override
	public String getPluginName() {
		return PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return PLUGIN_ID;
	}

	@Override
	public void displayToolchainResults(final IToolchainData<RunDefinition> toolchain,
			final Map<String, List<IResult>> results) {
		final ResultSummarizer summarizer = new ResultSummarizer(results);
		switch (summarizer.getResultSummary()) {
		case CORRECT:
			mTrayIconNotifier.showTrayBalloon("Program is correct", "Ultimate proved your program to be correct!",
					SWT.ICON_INFORMATION);
			break;
		case INCORRECT:
			mTrayIconNotifier.showTrayBalloon("Program is incorrect", "Ultimate proved your program to be incorrect!",
					SWT.ICON_WARNING);
			break;
		default:
			mTrayIconNotifier.showTrayBalloon("Program could not be checked",
					"Ultimate could not prove your program: " + summarizer.getResultDescription(),
					SWT.ICON_INFORMATION);
			break;
		}
	}

	@Override
	public void displayException(final IToolchainData<RunDefinition> toolchain, final String description,
			final Throwable ex) {
		// TODO: Log exceptions
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return null;
	}

	public void setAfterRerunCurrentToolchain(final IToolchain<RunDefinition> toolchain) {
		if (mCurrentToolchain != null && !mCurrentToolchain.equals(toolchain)) {
			mCore.releaseToolchain(mCurrentToolchain);
		}
		mCurrentToolchain = toolchain;
	}

	public IToolchain<RunDefinition> getCurrentToolchain() {
		return mCurrentToolchain;
	}

	public ILoggingService getLoggingService() {
		return mLoggingService;
	}

	@Override
	public void prerun(final IToolchainData<RunDefinition> tcData) {
		// not needed
	}
}
