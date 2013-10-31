package de.uni_freiburg.informatik.ultimate.gui.actions;

import java.io.File;
import java.io.FileNotFoundException;

import javax.xml.bind.JAXBException;

import de.uni_freiburg.informatik.ultimate.core.api.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.Toolchain;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainJob;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.gui.GuiController;
import de.uni_freiburg.informatik.ultimate.gui.contrib.PreludeContribution;
import de.uni_freiburg.informatik.ultimate.gui.interfaces.IImageKeys;
import de.uni_freiburg.informatik.ultimate.gui.interfaces.IPreferencesKeys;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.eclipse.ui.actions.ActionFactory.IWorkbenchAction;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.xml.sax.SAXException;

/**
 * 
 * @author dietsch
 * @version 0.0.1 $LastChangedDate: 2013-10-28 15:45:22 +0100 (Mo, 28 Okt 2013)
 *          $ $LastChangedBy$LastChangedRevision: 10093 $
 */

public class ResetAndRedoToolChainAction extends Action implements
		IWorkbenchAction {

	public static final String ID = "de.uni_freiburg.informatik.ultimate.gui.ResetAndRedoToolChainAction";
	private static final String LABEL = "Reset and re-execute";

	private IWorkbenchWindow mWorkbenchWindow;
	private Logger mLogger;
	private ICore mCore;
	private IController mController;

	public ResetAndRedoToolChainAction(final IWorkbenchWindow window,
			final ICore icore, final IController controller) {
		mLogger = UltimateServices.getInstance().getControllerLogger();
		mWorkbenchWindow = window;
		mCore = icore;
		mController = controller;
		setId(ID);
		setText(LABEL);
		setImageDescriptor(AbstractUIPlugin.imageDescriptorFromPlugin(
				GuiController.sPLUGINID, IImageKeys.REEXEC));
	}

	/**
	 * ! This is a generated comment ! The action has been activated. The
	 * argument of the method represents the 'real' action sitting in the
	 * workbench UI.
	 * 
	 * @see IWorkbenchWindowActionDelegate#run
	 */
	public final void run() {
		boolean rerun = mCore.canRerun();
		File prelude = PreludeContribution.getPreludeFile();
		PreludeProvider preludeprovider = prelude == null ? null
				: new PreludeProvider(prelude.getAbsolutePath());
		if (!rerun) {
			IEclipsePreferences prefscope = InstanceScope.INSTANCE
					.getNode(GuiController.sPLUGINID);
			String filterpath = prefscope.get(IPreferencesKeys.LASTPATH, null);
			if (filterpath != null) {
				File inputfile = new File(filterpath);
				if (inputfile.canRead()) {
					String toolchainxml = prefscope.get(
							IPreferencesKeys.LASTTOOLCHAINPATH, null);
					if (toolchainxml != null) {
						try {
							Toolchain toolchain = new Toolchain(toolchainxml);
							mCore.setToolchain(toolchain);
							mCore.setInputFile(inputfile);
							// In this case, we have to initiate the parser!
							mCore.initiateParser(preludeprovider);
							rerun = true;
						} catch (FileNotFoundException e) {
							MessageDialog.openError(
									mWorkbenchWindow.getShell(),
									"Error Occurred",
									"Please run a toolchain before trying to "
											+ "rerun it.");
						} catch (JAXBException e) {
							MessageDialog.openError(
									mWorkbenchWindow.getShell(),
									"Error Occurred",
									"Please run a toolchain before trying to "
											+ "rerun it.");
						} catch (SAXException e) {
							MessageDialog.openError(
									mWorkbenchWindow.getShell(),
									"Error Occurred",
									"Please run a toolchain before trying to "
											+ "rerun it.");
						}
					}
				}
			}
		}
		if (!rerun) {
			mWorkbenchWindow.getWorkbench().getDisplay()
					.asyncExec(new Runnable() {

						@Override
						public void run() {
							MessageDialog.openError(
									mWorkbenchWindow.getShell(),
									"Error Occurred",
									"Please run a toolchain before trying to "
											+ "rerun it.");
						}

					});
			return;
		}
		mLogger.info("Running Reset and re-execute...");

		ToolchainJob tcj = new ToolchainJob("Processing Toolchain", mCore,
				mController, null, ToolchainJob.Chain_Mode.RERUN_TOOLCHAIN,
				preludeprovider);
		tcj.schedule();

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
