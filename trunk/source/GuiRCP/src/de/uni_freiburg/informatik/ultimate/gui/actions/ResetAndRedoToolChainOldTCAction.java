package de.uni_freiburg.informatik.ultimate.gui.actions;


import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;

import javax.xml.bind.JAXBException;

import de.uni_freiburg.informatik.ultimate.core.api.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.Toolchain;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainJob;
import de.uni_freiburg.informatik.ultimate.ep.ExtensionPoints;
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

public class ResetAndRedoToolChainOldTCAction extends Action implements IWorkbenchAction {

	public static final String ID = "de.uni_freiburg.informatik.ultimate.gui.ResetAndRedoToolChainOldTCAction";
	private static final String LABEL = "Execute current Toolchain on new file(s)";

	private IWorkbenchWindow workbenchWindow;
	private static Logger logger = UltimateServices.getInstance().getControllerLogger();
	private ICore core;

	public ResetAndRedoToolChainOldTCAction(final IWorkbenchWindow window, final ICore icore) {
		this.workbenchWindow = window;
        this.core = icore;
        setId(ID);
        setText(LABEL);
        setImageDescriptor(AbstractUIPlugin.imageDescriptorFromPlugin(GuiController.s_PLUGIN_ID,
                IImageKeys.REEXECOLDTC));
	}

	/**
	 * ! This is a generated comment !
	 * The action has been activated. The argument of the method represents the
	 * 'real' action sitting in the workbench UI.
	 * 
	 * @see IWorkbenchWindowActionDelegate#run
	 */
	public final void run() {
		boolean rerun = core.canRerun();
		File prelude = PreludeContribution.getPreludeFile();
		PreludeProvider preludeprovider = prelude == null ? 
				null : new PreludeProvider(prelude.getAbsolutePath());
			if (!rerun) {
			InstanceScope iscope = new InstanceScope();
	        IEclipsePreferences prefscope = iscope.getNode(GuiController.s_PLUGIN_ID);
    		String toolchainxml = prefscope.get(IPreferencesKeys.LASTTOOLCHAINPATH, null);
    		if (toolchainxml != null) {
    			try {
        			Toolchain toolchain = new Toolchain(toolchainxml);
        			core.setToolchain(toolchain);
        			rerun = true;
    			} catch (FileNotFoundException e) {
    				MessageDialog.openError(workbenchWindow.getShell(),
							"Error Occurred",
							"Please run a toolchain on a file before "+
							"trying to rerun it on a different file.");
				} catch (JAXBException e) {
					MessageDialog.openError(workbenchWindow.getShell(),
							"Error Occurred",
							"Please run a toolchain on a file before "+
							"trying to rerun it on a different file.");
				} catch (SAXException e) {
					MessageDialog.openError(workbenchWindow.getShell(),
							"Error Occurred",
							"Please run a toolchain on a file before "+
							"trying to rerun it on a different file.");
				}
    		}
        }
		if (!rerun) {
			workbenchWindow.getWorkbench().getDisplay().asyncExec(
					new Runnable() {

						@Override
						public void run() {
							MessageDialog.openError(workbenchWindow.getShell(),
									"Error Occurred",
									"Please run a toolchain on a file before "+
									"trying to rerun it on a different file.");
						}
				
			});
			return;
		}
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
                logger.error("Cannot create extension "+element, e);
            }
        }

        FileDialog fd = new FileDialog(workbenchWindow.getShell(), SWT.OPEN
				| SWT.MULTI);
		fd.setText(LoadSourceFilesAction.s_DIALOG_NAME);
        
        ArrayList<String> extensions = new ArrayList<String>();
        ArrayList<String> names = new ArrayList<String>();
        
		//String[] extensions = new String[sourceplugins.size() + 1];
		//String[] names = new String[sourceplugins.size() + 1];

        extensions.add("*.*");
        names.add("All");
        
        for(ISource source : sourceplugins) {
            for(String s : source.getFileTypes()) {
                extensions.add("*." + s);
                names.add(source.getName() + " (*." + s + ")");
            }
            //extensions[sourceCount] = source.getFileTypes();
            //names[sourceCount++] = source.getName();
        }
        InstanceScope iscope = new InstanceScope();
        ScopedPreferenceStore store = new ScopedPreferenceStore(iscope,GuiController.s_PLUGIN_ID);
        IEclipsePreferences prefscope = iscope.getNode(GuiController.s_PLUGIN_ID);
        String filterpath = prefscope.get(IPreferencesKeys.LASTPATH, null);
		fd.setFilterExtensions(extensions.toArray(new String[extensions.size()]));
		fd.setFilterNames(names.toArray(new String[names.size()]));
		fd.setFileName(filterpath);
		String fp = fd.open();
		if( fp != null ) {
			prefscope.put(IPreferencesKeys.LASTPATH,fp);
			try {
				store.save();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
//		String[] files = fd.getFileNames();
//        
//		
//		
//        if (files.length != 0 && !files[0].contains(File.separator)) {
//            for (int i=0;i<files.length;++i) {
//                files[i] = fd.getFilterPath() + File.separator + files[i]; 
//            }
//        }
		//String filterpath = fd.getFilterPath();

		// jakobro: Don't know what this is. Please correct
		// dd: obsolete because steerable core is changing right now
		// co: now changing so it works with ICore
		/*
		 * if (files.length > 0 && filterpath != null) {
		 * steerableCore.loadSourcefiles(files, filterpath); }
		 */
		// cast String to files ... and call core
//		if (files.length != 0){
//			final File[] f=new File[files.length];
//			for (int i=0; i < f.length ; i++)
//				f[i]= new File(files[i]);
//			logger.info("Running Reset and re-execute...");
//		if(workbenchWindow.getActivePage().getActiveEditor() == null){
//			logger.info("No active editor present");
//			return;
//		}
		
//			logger.info("Disposing running editors...");
//			for (IEditorReference editor : workbenchWindow.getActivePage().getEditorReferences()){
//				workbenchWindow.getActivePage().closeEditor(editor.getEditor(false), false);
//			}
		if (fp != null) {
			ToolchainJob tcj = new ToolchainJob("Processing Toolchain", this.core, this.workbenchWindow, new File(fp), 
					ToolchainJob.Chain_Mode.RUN_OLDTOOLCHAIN, preludeprovider);
			tcj.schedule();

		}
	}


	/**
	 * ! This is a generated comment !
	 * Selection in the workbench has been changed. We can change the state of
	 * the 'real' action here if we want, but this can only happen after the
	 * delegate has been created.
	 * 
	 * @see IWorkbenchWindowActionDelegate#selectionChanged
	 */
	public void selectionChanged(IAction action, ISelection selection) {
	}

	/**
	 * ! This is a generated comment !
	 * We can use this method to dispose of any system resources we previously
	 * allocated.
	 * 
	 * @see IWorkbenchWindowActionDelegate#dispose
	 */
	public void dispose() {
	}




}
