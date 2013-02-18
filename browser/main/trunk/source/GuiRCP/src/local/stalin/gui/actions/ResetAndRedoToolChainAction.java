package local.stalin.gui.actions;


import java.io.File;
import java.io.FileNotFoundException;

import javax.xml.bind.JAXBException;

import local.stalin.core.api.PreludeProvider;
import local.stalin.core.api.StalinServices;
import local.stalin.core.coreplugin.toolchain.Toolchain;
import local.stalin.core.coreplugin.toolchain.ToolchainJob;
import local.stalin.ep.interfaces.ICore;
import local.stalin.gui.GuiController;
import local.stalin.gui.contrib.PreludeContribution;
import local.stalin.gui.interfaces.IImageKeys;
import local.stalin.gui.interfaces.IPreferencesKeys;

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
 * @version 0.0.1 
 * $LastChangedDate: 2010-05-05 20:56:04 +0200 (Mi, 05. Mai 2010) $
 * $LastChangedBy: dietsch 
 * $LastChangedRevision: 2378 $
 */

public class ResetAndRedoToolChainAction extends Action implements IWorkbenchAction {

	public static final String ID = "local.stalin.gui.ResetAndRedoToolChainAction";
	private static final String LABEL = "Reset and re-execute";

	private IWorkbenchWindow workbenchWindow;
	private static Logger logger = StalinServices.getInstance().getControllerLogger();
	private ICore core;

	public ResetAndRedoToolChainAction(final IWorkbenchWindow window, final ICore icore) {
		this.workbenchWindow = window;
        this.core = icore;
        setId(ID);
        setText(LABEL);
        setImageDescriptor(AbstractUIPlugin.imageDescriptorFromPlugin(GuiController.s_PLUGIN_ID,
                IImageKeys.REEXEC));
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
	        String filterpath = prefscope.get(IPreferencesKeys.LASTPATH, null);
	        if (filterpath != null) {
	        	File inputfile = new File(filterpath);
	        	if (inputfile.canRead()) {
	        		String toolchainxml = prefscope.get(IPreferencesKeys.LASTTOOLCHAINPATH, null);
	        		if (toolchainxml != null) {
	        			try {
		        			Toolchain toolchain = new Toolchain(toolchainxml);
		        			core.setToolchain(toolchain);
		        			core.setInputFile(inputfile);
		        			// In this case, we have to initiate the parser!
		        			core.initiateParser(preludeprovider);
		        			rerun = true;
	        			} catch (FileNotFoundException e) {
	        				MessageDialog.openError(workbenchWindow.getShell(),
									"Error Occurred",
									"Please run a toolchain before trying to "+
									"rerun it.");
						} catch (JAXBException e) {
							MessageDialog.openError(workbenchWindow.getShell(),
									"Error Occurred",
									"Please run a toolchain before trying to "+
									"rerun it.");
						} catch (SAXException e) {
							MessageDialog.openError(workbenchWindow.getShell(),
									"Error Occurred",
									"Please run a toolchain before trying to "+
									"rerun it.");
						}
	        		}
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
									"Please run a toolchain before trying to "+
									"rerun it.");
						}
				
			});
			return;
		}
		logger.info("Running Reset and re-execute...");
//		if(workbenchWindow.getActivePage().getActiveEditor() == null){
//			logger.info("No active editor present");
//			return;
//		}
		
//		logger.info("Disposing running editors...");
//		for (IEditorReference editor : workbenchWindow.getActivePage().getEditorReferences()){
//			workbenchWindow.getActivePage().closeEditor(editor.getEditor(false), false);
//		}
		ToolchainJob tcj = new ToolchainJob("Processing Toolchain", this.core, this.workbenchWindow, null, 
				ToolchainJob.Chain_Mode.RERUN_TOOLCHAIN, preludeprovider);
		tcj.schedule();

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
