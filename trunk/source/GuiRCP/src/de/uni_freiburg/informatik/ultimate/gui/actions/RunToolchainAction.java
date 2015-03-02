package de.uni_freiburg.informatik.ultimate.gui.actions;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.regex.Pattern;

import javax.xml.bind.JAXBException;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.ep.ExtensionPoints;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.gui.GuiController;
import de.uni_freiburg.informatik.ultimate.gui.interfaces.IPreferencesKeys;

public abstract class RunToolchainAction extends Action {

	protected final IWorkbenchWindow mWorkbenchWindow;
	protected final Logger mLogger;
	protected final ICore mCore;
	protected final GuiController mController;

	public RunToolchainAction(Logger logger, IWorkbenchWindow window, ICore icore, GuiController controller, String id,
			String label, String imageFilePath) {
		super();
		mLogger = logger;
		mWorkbenchWindow = window;
		mCore = icore;
		mController = controller;
		setId(id);
		setText(label);
		setImageDescriptor(AbstractUIPlugin.imageDescriptorFromPlugin(GuiController.sPLUGINID, imageFilePath));
	}

	protected File[] getLastInputFiles() {
		String lastInputFilePath = new UltimatePreferenceStore(GuiController.sPLUGINID)
				.getString(IPreferencesKeys.LASTPATH);
		if (lastInputFilePath == null || lastInputFilePath.isEmpty()) {
			// there is no last input file saved
			return null;
		}
		String[] singlePaths = lastInputFilePath.split(Pattern.quote(File.pathSeparator));
		ArrayList<File> rtr = new ArrayList<>();

		for (String path : singlePaths) {
			File f = new File(path);
			if (f.canRead()) {
				// there is an inputfile saved and it is still there
				rtr.add(f);
			}
		}
		if (rtr.size() > 0) {
			return rtr.toArray(new File[0]);
		}
		return null;
	}

	protected ToolchainData getLastToolchainData() {
		String toolchainxml = new UltimatePreferenceStore(GuiController.sPLUGINID)
				.getString(IPreferencesKeys.LASTTOOLCHAINPATH);
		if (toolchainxml == null || toolchainxml.isEmpty()) {
			// there is no last toolchain saved
			return null;
		}
		try {
			return new ToolchainData(toolchainxml);
		} catch (FileNotFoundException | JAXBException | SAXException e) {
			return null;
		}
	}

	protected File[] getInputFilesFromUser(String dialogTitle) {

		ArrayList<String> extensions = new ArrayList<String>();
		ArrayList<String> names = new ArrayList<String>();

		extensions.add("*.*");
		names.add("All");

		for (ISource source : getAvailableSourcePlugins()) {
			for (String s : source.getFileTypes()) {
				extensions.add("*." + s);
				names.add(source.getPluginName() + " (*." + s + ")");
			}
		}

		FileDialog fd = new FileDialog(mWorkbenchWindow.getShell(), SWT.OPEN | SWT.MULTI);
		fd.setText(dialogTitle);

		UltimatePreferenceStore prefStore = new UltimatePreferenceStore(GuiController.sPLUGINID);

		fd.setFilterExtensions(extensions.toArray(new String[extensions.size()]));
		fd.setFilterNames(names.toArray(new String[names.size()]));

		File[] lastInput = getLastInputFiles();
		if (lastInput != null && lastInput.length > 0) {
			fd.setFileName(lastInput[0].getAbsolutePath());
		}

		fd.open();
		String[] fileNames = fd.getFileNames();
		String path = fd.getFilterPath();

		if (fileNames != null && fileNames.length > 0) {
			StringBuilder sb = new StringBuilder();
			for (String name : fileNames) {
				sb.append(path).append(File.separator).append(name).append(File.pathSeparator);
			}
			sb.delete(sb.length() - 1, sb.length());
			prefStore.put(IPreferencesKeys.LASTPATH, sb.toString());
		}

		ArrayList<File> rtr = new ArrayList<>();
		for (String filename : fileNames) {
			File file = new File(path + File.separator + filename);
			if (file.isFile() && file.exists()) {
				rtr.add(file);
			}
		}
		return rtr.toArray(new File[0]);
	}

	private Collection<ISource> getAvailableSourcePlugins() {
		ArrayList<ISource> sourceplugins = new ArrayList<ISource>();
		IExtensionRegistry reg = Platform.getExtensionRegistry();

		IConfigurationElement[] configElements_source = reg.getConfigurationElementsFor(ExtensionPoints.EP_SOURCE);
		// iterate through every config element
		for (IConfigurationElement element : configElements_source) {
			try {
				// create class from plugin
				ISource source = (ISource) element.createExecutableExtension("class");
				// and add to plugin ArrayList
				sourceplugins.add(source);
			} catch (CoreException e) {
				mLogger.error("Cannot create extension " + element, e);
			}
		}
		return sourceplugins;
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