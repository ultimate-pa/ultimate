package de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.export;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.editor.PrefuseEditorInput;
import org.apache.log4j.Logger;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;

import prefuse.Display;

/**
 * This class creates a control which allows the user to save a the prefuse
 * visualization
 * 
 * @author keil
 * @version 0.0.1 
 * $LastChangedDate: 2008-03-07 13:50:06 +0100 (Fr, 07 Mrz 2008) $
 * $LastChangedBy: keilr $
 * $LastChangedRevision: 495 $
 */
public class SaveDisplayAction extends Action implements
		IWorkbenchWindowActionDelegate {
	public static final String ID = "de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.export.SaveDisplayAction";

	private IWorkbenchWindow workbenchWindow;
	private static Logger logger = UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);

	/**
	 * Constructor
	 */
	public SaveDisplayAction() {
	}

	/**
	 * ! This is a generated comment ! The action has been activated. The
	 * argument of the method represents the 'real' action sitting in the
	 * workbench UI.
	 * 
	 * @see IWorkbenchWindowActionDelegate#run
	 */
	public void run(IAction action) {
		if (workbenchWindow.getActivePage().getActiveEditor() == null) {
			logger.info("No active editor present");
			return;
		}
		if (workbenchWindow.getActivePage().getActiveEditor().getEditorInput() instanceof PrefuseEditorInput) {
			try {
				PrefuseEditorInput input = (PrefuseEditorInput) workbenchWindow
						.getActivePage().getActiveEditor().getEditorInput();
				Display display = input.getDisplay();
				DisplayExport dEx = new DisplayExport(display);
				dEx.save();

			} catch (Exception ex) {
				logger.error("General exception: " + ex + " "
						+ ex.getStackTrace() + " " + ex.getClass());
			}
		} else {
			logger.warn("Wrong type: Expected \"PrefuseEditorInput\" got "
					+ workbenchWindow.getActivePage().getActiveEditor()
							.getEditorInput().getClass().toString());
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

	/**
	 * 
	 * We will cache window object in order to be able to provide parent shell
	 * for the message dialog.
	 * 
	 * @see IWorkbenchWindowActionDelegate#init
	 * 
	 * We will also initialize the logger (cutnpaste from core.application)
	 */
	public void init(IWorkbenchWindow window) {
		this.workbenchWindow = window;
	}
}