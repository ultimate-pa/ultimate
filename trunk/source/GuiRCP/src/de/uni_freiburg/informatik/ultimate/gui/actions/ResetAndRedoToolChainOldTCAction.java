package de.uni_freiburg.informatik.ultimate.gui.actions;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;

import javax.xml.bind.JAXBException;

import de.uni_freiburg.informatik.ultimate.core.api.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.BasicToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.Toolchain;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.DefaultToolchainJob;
import de.uni_freiburg.informatik.ultimate.ep.ExtensionPoints;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.gui.GuiController;
import de.uni_freiburg.informatik.ultimate.gui.contrib.PreludeContribution;
import de.uni_freiburg.informatik.ultimate.gui.interfaces.IImageKeys;
import de.uni_freiburg.informatik.ultimate.gui.interfaces.IPreferencesKeys;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.eclipse.ui.actions.ActionFactory.IWorkbenchAction;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.eclipse.ui.preferences.ScopedPreferenceStore;
import org.xml.sax.SAXException;

/**
 * 
 * @author christj
 * @version 0.0.1
 */

public class ResetAndRedoToolChainOldTCAction extends Action implements
		IWorkbenchAction {

	public static final String ID = "de.uni_freiburg.informatik.ultimate.gui.ResetAndRedoToolChainOldTCAction";
	private static final String LABEL = "Execute current Toolchain on new file(s)";

	private IWorkbenchWindow mWorkbenchWindow;
	private static Logger logger = UltimateServices.getInstance()
			.getControllerLogger();
	private ICore mCore;
	private IController mController;

	public ResetAndRedoToolChainOldTCAction(final IWorkbenchWindow window,
			final ICore icore, final IController controller) {
		mWorkbenchWindow = window;
		mCore = icore;
		mController = controller;
		setId(ID);
		setText(LABEL);
		setImageDescriptor(AbstractUIPlugin.imageDescriptorFromPlugin(
				GuiController.sPLUGINID, IImageKeys.REEXECOLDTC));
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
			IScopeContext iscope = InstanceScope.INSTANCE;
			IEclipsePreferences prefscope = iscope
					.getNode(GuiController.sPLUGINID);
			String toolchainxml = prefscope.get(
					IPreferencesKeys.LASTTOOLCHAINPATH, null);
			if (toolchainxml != null) {
				try {
					Toolchain toolchain = new Toolchain(toolchainxml);
					mCore.setToolchain(toolchain);
					rerun = true;
				} catch (FileNotFoundException e) {
					MessageDialog
							.openError(
									mWorkbenchWindow.getShell(),
									"Error Occurred",
									"Please run a toolchain on a file before "
											+ "trying to rerun it on a different file.");
				} catch (JAXBException e) {
					MessageDialog
							.openError(
									mWorkbenchWindow.getShell(),
									"Error Occurred",
									"Please run a toolchain on a file before "
											+ "trying to rerun it on a different file.");
				} catch (SAXException e) {
					MessageDialog
							.openError(
									mWorkbenchWindow.getShell(),
									"Error Occurred",
									"Please run a toolchain on a file before "
											+ "trying to rerun it on a different file.");
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
									"Please run a toolchain on a file before "
											+ "trying to rerun it on a different file.");
						}

					});
			return;
		}
		ArrayList<ISource> sourceplugins = new ArrayList<ISource>();
		IExtensionRegistry reg = Platform.getExtensionRegistry();

		IConfigurationElement[] configElements_source = reg
				.getConfigurationElementsFor(ExtensionPoints.EP_SOURCE);
		// iterate through every config element
		for (IConfigurationElement element : configElements_source) {
			try {
				// create class from plugin
				ISource source = (ISource) element
						.createExecutableExtension("class");
				// and add to plugin ArrayList
				sourceplugins.add(source);
			} catch (CoreException e) {
				logger.error("Cannot create extension " + element, e);
			}
		}

		FileDialog fd = new FileDialog(mWorkbenchWindow.getShell(), SWT.OPEN
				| SWT.MULTI);
		fd.setText(LoadSourceFilesAction.s_DIALOG_NAME);

		ArrayList<String> extensions = new ArrayList<String>();
		ArrayList<String> names = new ArrayList<String>();

		extensions.add("*.*");
		names.add("All");

		for (ISource source : sourceplugins) {
			for (String s : source.getFileTypes()) {
				extensions.add("*." + s);
				names.add(source.getName() + " (*." + s + ")");
			}
		}
		IScopeContext iscope = InstanceScope.INSTANCE;
		ScopedPreferenceStore store = new ScopedPreferenceStore(iscope,
				GuiController.sPLUGINID);
		IEclipsePreferences prefscope = iscope.getNode(GuiController.sPLUGINID);
		String filterpath = prefscope.get(IPreferencesKeys.LASTPATH, null);
		fd.setFilterExtensions(extensions.toArray(new String[extensions.size()]));
		fd.setFilterNames(names.toArray(new String[names.size()]));
		fd.setFileName(filterpath);
		String fp = fd.open();
		if (fp != null) {
			prefscope.put(IPreferencesKeys.LASTPATH, fp);
			try {
				store.save();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}

		if (fp != null) {
			BasicToolchainJob tcj = new DefaultToolchainJob("Processing Toolchain", mCore,
					mController, BasicToolchainJob.ChainMode.RUN_OLDTOOLCHAIN,
					new File(fp), preludeprovider);
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
