package de.uni_freiburg.informatik.ultimate.gui.actions;

import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;

import org.eclipse.jface.action.Action;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.actions.ActionFactory.IWorkbenchAction;

public class LoadSettingsAction extends Action implements IWorkbenchAction {

	public static final String s_ID = "de.uni_freiburg.informatik.ultimate.gui.LoadSetings";
	
	private ICore mCore;
	private IWorkbenchWindow mWindow;

	public LoadSettingsAction(final IWorkbenchWindow window, final ICore icore) {
		setId(s_ID);
		setText("Load settings");
		setToolTipText("Loads previously saved settings from a file");
		mCore = icore;
		mWindow = window;
	}

	public void run() {
		FileDialog fd = new FileDialog(mWindow.getShell(), SWT.OPEN);
		mCore.loadPreferences(fd.open());
	}

	@Override
	public void dispose() {
		// TODO Auto-generated method stub

	}

}
