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
import de.uni_freiburg.informatik.ultimate.gui.GuiController;
import de.uni_freiburg.informatik.ultimate.gui.GuiToolchainJob;
import de.uni_freiburg.informatik.ultimate.gui.contrib.PreludeContribution;
import de.uni_freiburg.informatik.ultimate.gui.interfaces.IImageKeys;

/**
 * Execute old toolchain on new file(s)
 * 
 * @author dietsch
 */

public class ResetAndRedoToolChainOldTCAction extends RunToolchainAction implements IWorkbenchAction {

	private static final String ID = "de.uni_freiburg.informatik.ultimate.gui.ResetAndRedoToolChainOldTCAction";
	private static final String LABEL = "Execute current Toolchain on new file(s)";

	public ResetAndRedoToolChainOldTCAction(final IWorkbenchWindow window, final ICore icore,
			final GuiController controller, final Logger logger) {
		super(logger, window, icore, controller, ID, LABEL, IImageKeys.REEXECOLDTC);
	}

	/**
	 * ! This is a generated comment ! The action has been activated. The
	 * argument of the method represents the 'real' action sitting in the
	 * workbench UI.
	 * 
	 * @see IWorkbenchWindowActionDelegate#run
	 */
	public final void run() {

		// Execute old toolchain on new input file(s)

		File prelude = PreludeContribution.getPreludeFile();
		ToolchainData toolchain = getLastToolchainData();

		if (toolchain == null) {
			MessageDialog.openError(mWorkbenchWindow.getShell(), "Error Occurred", "There is no old toolchain");
			return;
		}

		String inputFile = getInputFileFromUser("Select input file...");
		if (inputFile == null) {
			return;
		}

		BasicToolchainJob tcj = new GuiToolchainJob("Processing Toolchain", mCore, mController, mLogger, toolchain,
				new File(inputFile), prelude == null ? null : new PreludeProvider(prelude.getAbsolutePath(), mLogger));
		tcj.schedule();

	}
}
