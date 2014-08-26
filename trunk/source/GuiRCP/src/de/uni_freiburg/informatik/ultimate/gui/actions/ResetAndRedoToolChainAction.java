package de.uni_freiburg.informatik.ultimate.gui.actions;

import java.io.File;

import org.apache.log4j.Logger;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.eclipse.ui.actions.ActionFactory.IWorkbenchAction;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.BasicToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.core.services.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IToolchain;
import de.uni_freiburg.informatik.ultimate.gui.GuiController;
import de.uni_freiburg.informatik.ultimate.gui.GuiToolchainJob;
import de.uni_freiburg.informatik.ultimate.gui.contrib.PreludeContribution;
import de.uni_freiburg.informatik.ultimate.gui.interfaces.IImageKeys;

/**
 * 
 * @author dietsch
 * @version 0.0.1 $LastChangedDate: 2013-10-28 15:45:22 +0100 (Mo, 28 Okt 2013)
 *          $ $LastChangedBy$LastChangedRevision: 10093 $
 */

public class ResetAndRedoToolChainAction extends RunToolchainAction implements IWorkbenchAction {

	private static final String ID = "de.uni_freiburg.informatik.ultimate.gui.ResetAndRedoToolChainAction";
	private static final String LABEL = "Reset and re-execute";

	public ResetAndRedoToolChainAction(final IWorkbenchWindow window, final ICore icore,
			final GuiController controller, Logger logger) {
		super(logger, window, icore, controller,ID,LABEL,IImageKeys.REEXEC);
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
				// ok, that also didnt work, we give up
				MessageDialog.openError(mWorkbenchWindow.getShell(), "Error Occurred",
						"Please run a toolchain before trying to " + "rerun it.");
				return;
			}
			tcj.schedule();
		}
	}
	
	private BasicToolchainJob getToolchainJobFromPreferences() {
		File lastInputFile = getLastInputFile();
		if (lastInputFile == null) {
			return null;
		}

		File prelude = PreludeContribution.getPreludeFile();
		ToolchainData toolchain = getLastToolchainData();

		if (toolchain == null) {
			MessageDialog.openError(mWorkbenchWindow.getShell(), "Error Occurred",
					"Please run a toolchain before trying to " + "rerun it.");
			return null;
		}
		return new GuiToolchainJob("Re-running toolchain from preferences...", mCore, mController, mLogger, toolchain,
				lastInputFile, prelude == null ? null : new PreludeProvider(prelude.getAbsolutePath(), mLogger));
	}
}
