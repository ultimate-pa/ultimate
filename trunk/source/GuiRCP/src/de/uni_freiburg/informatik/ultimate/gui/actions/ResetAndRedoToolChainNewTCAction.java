package de.uni_freiburg.informatik.ultimate.gui.actions;


import java.io.File;

import de.uni_freiburg.informatik.ultimate.core.api.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainJob;
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

/**
 * 
 * @author christj
 * @version 0.0.1 
 */

public class ResetAndRedoToolChainNewTCAction extends Action implements IWorkbenchAction {

	public static final String ID = "de.uni_freiburg.informatik.ultimate.gui.ResetAndRedoToolChainNewTCAction";
	private static final String LABEL = "Execute new Toolchain on file(s)";

	private IWorkbenchWindow workbenchWindow;
	private static Logger logger = UltimateServices.getInstance().getControllerLogger();
	private ICore core;

	public ResetAndRedoToolChainNewTCAction(final IWorkbenchWindow window, final ICore icore) {
		this.workbenchWindow = window;
        this.core = icore;
        setId(ID);
        setText(LABEL);
        setImageDescriptor(AbstractUIPlugin.imageDescriptorFromPlugin(GuiController.s_PLUGIN_ID,
                IImageKeys.REEXECNEWTC));
	}

	/**
	 * ! This is a generated comment !
	 * The action has been activated. The argument of the method represents the
	 * 'real' action sitting in the workbench UI.
	 * 
	 * @see IWorkbenchWindowActionDelegate#run
	 */
	public final void run() {
		boolean rerun = core.hasInputFiles();
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
        			core.setInputFile(inputfile);
        			// In this case, we have to initiate the parser!
        			core.initiateParser(preludeprovider);
        			rerun = true;
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
									"trying to run a different toolchain on "+
									"the same input file.");
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
				ToolchainJob.Chain_Mode.RUN_NEWTOOLCHAIN, preludeprovider);
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
