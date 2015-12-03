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

import javax.xml.bind.JAXBException;

import org.apache.log4j.Logger;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PlatformUI;
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.model.ILoggingService;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IToolchain;
import de.uni_freiburg.informatik.ultimate.gui.advisors.ApplicationWorkbenchAdvisor;
import de.uni_freiburg.informatik.ultimate.gui.dialogs.AnalysisChooseDialog;
import de.uni_freiburg.informatik.ultimate.gui.dialogs.ModelChooseDialog;
import de.uni_freiburg.informatik.ultimate.gui.dialogs.ParserChooseDialog;

/**
 * GUIController is the IController implementation of the UltimateDebug GUI
 * 
 * @author dietsch
 * 
 */
public class GuiController implements IController {

	// public static final String sPLUGINID = "UltimateGui";
	public static final String sPLUGINID = GuiController.class.getPackage().getName();
	public static final String sPLUGINNAME = "Gui Controller";

	private Logger mLogger;
	private Display mDisplay;

	private volatile ISource mParser;
	private volatile ToolchainData mTools;
	private volatile List<String> mModels;

	private ICore mCore;
	private TrayIconNotifier mTrayIconNotifier;
	private IToolchain mCurrentToolchain;

	/**
	 * Initialization of Controller. The GUI is created here. Note: This methods
	 * blocks until the GUI is closed.
	 * 
	 * @return the exit code for the application
	 */
	public int init(ICore core, ILoggingService loggingService) {
		if(loggingService == null){
			throw new IllegalArgumentException("loggingService may not be null");
		}
		mLogger = loggingService.getControllerLogger();

		if (core == null) {
			mLogger.fatal("Initialization failed because no ICore instance was supplied");
			return -1;
		}

		mCore = core;
		mDisplay = PlatformUI.createDisplay();

		mParser = null;
		mModels = new ArrayList<String>();
		mLogger.debug("Creating Workbench ...");
		mLogger.debug("--------------------------------------------------------------------------------");
		int returnCode = -1;
		ApplicationWorkbenchAdvisor workbenchAdvisor = new ApplicationWorkbenchAdvisor();
		if (mDisplay != null && workbenchAdvisor != null) {
			mTrayIconNotifier = new TrayIconNotifier(workbenchAdvisor);
			workbenchAdvisor.init(mCore, mTrayIconNotifier, this, mLogger);
			try {
				returnCode = PlatformUI.createAndRunWorkbench(mDisplay, workbenchAdvisor);
				mLogger.debug("GUI return code: " + returnCode);
				return returnCode;
			} catch (Exception ex) {
				mLogger.fatal("An exception occured", ex);
				return returnCode;
			} finally {
				setCurrentToolchain(null);
				mDisplay.dispose();
			}

		} else {
			mLogger.fatal("PlatformUI.createDisplay() delivered null-value, cannot create workbench, exiting...");

		}
		return returnCode;
	}

	public synchronized ISource selectParser(final Collection<ISource> parsers) {

		mDisplay.syncExec(new Runnable() {
			public void run() {
				Shell shell = new Shell(mDisplay);
				mParser = new ParserChooseDialog(shell, parsers).open();
			}
		});
		return mParser;
	}

	@SuppressWarnings("unchecked")
	public synchronized ToolchainData selectTools(final List<ITool> t) {
		return selectTools(t, Collections.EMPTY_LIST);
	}

	public synchronized ToolchainData selectTools(final List<ITool> t, final List<ITool> previous) {
		mDisplay.syncExec(new Runnable() {
			public void run() {
				Shell shell = new Shell(mDisplay);
				try {
					mTools = new AnalysisChooseDialog(mLogger, shell, t, previous).open();
				} catch (FileNotFoundException e) {
					MessageDialog.openError(shell, "An error occured", "Toolchain XML file was not found.");

				} catch (JAXBException e) {
					MessageDialog.openError(shell, "An error occured", "Toolchain XML file could not be validated.");
				} catch (SAXException e) {
					MessageDialog.openError(shell, "An error occured",
							"Toolchain XML file could not be properly parsed.");
				}
			}
		});
		return mTools;
	}

	public synchronized List<String> selectModel(final List<String> modelNames) {
		mDisplay.syncExec(new Runnable() {
			public void run() {
				Shell shell = new Shell(mDisplay);
				mModels = new ModelChooseDialog(shell, modelNames, "Choose the model").open();
			}
		});
		return mModels;
	}

	public String getPluginName() {
		return sPLUGINNAME;
	}

	public String getPluginID() {
		return sPLUGINID;
	}

	@Override
	public void displayToolchainResultProgramIncorrect() {
		mTrayIconNotifier.showTrayBalloon("Program is incorrect", "Ultimate proved your program to be incorrect!",
				SWT.ICON_WARNING);

	}

	@Override
	public void displayToolchainResultProgramCorrect() {
		mTrayIconNotifier.showTrayBalloon("Program is correct", "Ultimate proved your program to be correct!",
				SWT.ICON_INFORMATION);
	}

	@Override
	public void displayToolchainResultProgramUnknown(String description) {
		mTrayIconNotifier.showTrayBalloon("Program could not be checked", "Ultimate could not prove your program: "
				+ description, SWT.ICON_INFORMATION);

	}

	@Override
	public void displayException(final String description, final Throwable ex) {
		// mDisplay.asyncExec(new Runnable() {
		// public void run() {
		// Shell shell = new Shell(mDisplay);
		// // MessageDialog.openError(shell, "An error occured", description +
		// " " + ex.getMessage());
		// }
		// });

	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return null;
	}

	public void setCurrentToolchain(IToolchain toolchain) {
		if (mCurrentToolchain != null && mCurrentToolchain != toolchain) {
			mCore.releaseToolchain(mCurrentToolchain);
		}
		mCurrentToolchain = toolchain;
	}

	public IToolchain getCurrentToolchain() {
		return mCurrentToolchain;
	}
}
