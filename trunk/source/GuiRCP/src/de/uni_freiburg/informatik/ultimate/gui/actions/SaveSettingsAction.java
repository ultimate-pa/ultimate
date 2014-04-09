package de.uni_freiburg.informatik.ultimate.gui.actions;

import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;

import org.eclipse.jface.action.Action;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.actions.ActionFactory.IWorkbenchAction;

public class SaveSettingsAction extends Action implements IWorkbenchAction {

	public static final String s_ID = "de.uni_freiburg.informatik.ultimate.gui.SaveSetings";

	private ICore mCore;
	private IWorkbenchWindow mWindow;

	public SaveSettingsAction(final IWorkbenchWindow window, final ICore icore) {
		setId(s_ID);
		setText("Save settings");
		setToolTipText("Saves current settings to a file");
		mCore = icore;
		mWindow = window;
	}

	public void run() {
		FileDialog fd = new FileDialog(mWindow.getShell(), SWT.SAVE);
		mCore.savePreferences(fd.open());
	}

	@Override
	public void dispose() {
	}

}
