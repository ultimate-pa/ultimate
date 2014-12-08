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
import de.uni_freiburg.informatik.ultimate.core.services.ILoggingService;
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
		mDisplay.asyncExec(new Runnable() {
			public void run() {
				Shell shell = new Shell(mDisplay);
//				MessageDialog.openError(shell, "An error occured", description + " " + ex.getMessage());
			}
		});

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

	@Override
	protected void finalize() throws Throwable {
		setCurrentToolchain(null);
		super.finalize();
	}

}
