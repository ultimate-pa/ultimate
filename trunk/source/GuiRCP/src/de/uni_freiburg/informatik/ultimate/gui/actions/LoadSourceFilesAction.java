package de.uni_freiburg.informatik.ultimate.gui.actions;

import java.io.File;

import org.apache.log4j.Logger;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.actions.ActionFactory.IWorkbenchAction;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.BasicToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.services.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.gui.GuiController;
import de.uni_freiburg.informatik.ultimate.gui.GuiToolchainJob;
import de.uni_freiburg.informatik.ultimate.gui.contrib.PreludeContribution;
import de.uni_freiburg.informatik.ultimate.gui.interfaces.IImageKeys;

/**
 * The action that tells the core what files to open
 * 
 * may be do modification to listen for a response..
 * 
 * 
 * @author dietsch
 * 
 */
public class LoadSourceFilesAction extends RunToolchainAction implements IWorkbenchAction {

	private static final String s_ID = "de.uni_freiburg.informatik.ultimate.gui.LoadSourceFiles";
	private static final String s_DIALOG_NAME = "Open Source ... ";

	/**
	 * 
	 * @param window
	 *            the contexwindow
	 * @param ist
	 *            the steerablecore that will take the command
	 */
	public LoadSourceFilesAction(final IWorkbenchWindow window, final ICore icore, final GuiController controller,
			Logger logger) {
		super(logger, window, icore, controller, s_ID, s_DIALOG_NAME, IImageKeys.LOADSOURCEFILES);
	}

	/**
	 * the action opens a file dialog then passes the files for opening to the
	 * core
	 */
	public final void run() {
		String fp = getInputFileFromUser(s_DIALOG_NAME);

		if (fp != null) {
			File prelude = PreludeContribution.getPreludeFile();
			BasicToolchainJob tcj = new GuiToolchainJob("Processing Toolchain", mCore, mController, new File(fp),
					prelude == null ? null : new PreludeProvider(prelude.getAbsolutePath(), mLogger), mLogger);
			tcj.schedule();
		}
	}

}
