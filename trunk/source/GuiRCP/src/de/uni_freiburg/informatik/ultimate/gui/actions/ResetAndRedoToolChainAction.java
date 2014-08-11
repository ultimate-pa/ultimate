package de.uni_freiburg.informatik.ultimate.gui.actions;

import java.io.File;
import java.io.FileNotFoundException;

import javax.xml.bind.JAXBException;

import org.apache.log4j.Logger;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.eclipse.ui.actions.ActionFactory.IWorkbenchAction;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.BasicToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IToolchain;
import de.uni_freiburg.informatik.ultimate.gui.GuiController;
import de.uni_freiburg.informatik.ultimate.gui.GuiToolchainJob;
import de.uni_freiburg.informatik.ultimate.gui.contrib.PreludeContribution;
import de.uni_freiburg.informatik.ultimate.gui.interfaces.IImageKeys;
import de.uni_freiburg.informatik.ultimate.gui.interfaces.IPreferencesKeys;

/**
 * 
 * @author dietsch
 * @version 0.0.1 $LastChangedDate: 2013-10-28 15:45:22 +0100 (Mo, 28 Okt 2013)
 *          $ $LastChangedBy$LastChangedRevision: 10093 $
 */

public class ResetAndRedoToolChainAction extends Action implements IWorkbenchAction {

	public static final String ID = "de.uni_freiburg.informatik.ultimate.gui.ResetAndRedoToolChainAction";
	private static final String LABEL = "Reset and re-execute";

	private IWorkbenchWindow mWorkbenchWindow;
	private Logger mLogger;
	private ICore mCore;
	private GuiController mController;

	public ResetAndRedoToolChainAction(final IWorkbenchWindow window, final ICore icore,
			final GuiController controller, Logger logger) {
		mLogger = logger;
		mWorkbenchWindow = window;
		mCore = icore;
		mController = controller;
		setId(ID);
		setText(LABEL);
		setImageDescriptor(AbstractUIPlugin.imageDescriptorFromPlugin(GuiController.sPLUGINID, IImageKeys.REEXEC));
	}

	private BasicToolchainJob getToolchainJobFromPreferences() {
		// the core does not contain the last-run toolchain, but we can try to
		// retrieve it from the settings
		UltimatePreferenceStore prefs = new UltimatePreferenceStore(GuiController.sPLUGINID);
		String lastInputFilePath = prefs.getString(IPreferencesKeys.LASTPATH);
		if (lastInputFilePath == null || lastInputFilePath.isEmpty()) {
			// there is no last input file saved
			return null;
		}
		File lastInputFile = new File(lastInputFilePath);

		if (!lastInputFile.canRead()) {
			// there is an inputfile saved, but its not there anymore
			return null;
		}

		String toolchainxml = prefs.getString(IPreferencesKeys.LASTTOOLCHAINPATH);
		if (toolchainxml == null || toolchainxml.isEmpty()) {
			// there is no last toolchain saved
			return null;
		}

		File prelude = PreludeContribution.getPreludeFile();

		try {
			ToolchainData toolchain = new ToolchainData(toolchainxml);
			return new GuiToolchainJob("Re-running toolchain from preferences...", mCore, mController, mLogger,
					toolchain, lastInputFile, prelude == null ? null : new PreludeProvider(prelude.getAbsolutePath(),
							mLogger));

		} catch (FileNotFoundException e) {
			MessageDialog.openError(mWorkbenchWindow.getShell(), "Error Occurred",
					"Please run a toolchain before trying to " + "rerun it.");
		} catch (JAXBException e) {
			MessageDialog.openError(mWorkbenchWindow.getShell(), "Error Occurred",
					"Please run a toolchain before trying to " + "rerun it.");
		} catch (SAXException e) {
			MessageDialog.openError(mWorkbenchWindow.getShell(), "Error Occurred",
					"Please run a toolchain before trying to " + "rerun it.");
		}
		return null;
	}

	/**
	 * ! This is a generated comment ! The action has been activated. The
	 * argument of the method represents the 'real' action sitting in the
	 * workbench UI.
	 * 
	 * @see IWorkbenchWindowActionDelegate#run
	 */
	public final void run() {
		IToolchain tc = mController.getCurrentToolchain();

		if (tc != null) {
			// we have a toolchain that we can rerun
			BasicToolchainJob tcj = new GuiToolchainJob("Processing Toolchain", mCore, mController, mLogger, tc);
			tcj.schedule();
		} else {
			// we dont have a toolchain that we can rerun, but perhaps we can
			// construct one from our preferences
			BasicToolchainJob tcj = getToolchainJobFromPreferences();
			if (tcj == null) {
				//ok, that also didnt work, we give up
				MessageDialog.openError(mWorkbenchWindow.getShell(), "Error Occurred",
						"Please run a toolchain before trying to " + "rerun it.");
				return;
			}
			tcj.schedule();
		}
	}

	/**
	 * ! This is a generated comment ! Selection in the workbench has been
	 * changed. We can change the state of the 'real' action here if we want,
	 * but this can only happen after the delegate has been created.
	 * 
	 * @see IWorkbenchWindowActionDelegate#selectionChanged
	 */
	public void selectionChanged(IAction action, ISelection selection) {
	}

	/**
	 * ! This is a generated comment ! We can use this method to dispose of any
	 * system resources we previously allocated.
	 * 
	 * @see IWorkbenchWindowActionDelegate#dispose
	 */
	public void dispose() {
	}

}
