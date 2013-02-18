package de.uni_freiburg.informatik.ultimate.gui.actions;

import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;

import org.eclipse.jface.action.Action;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.actions.ActionFactory.IWorkbenchAction;

public class LoadSettingsAction extends Action implements IWorkbenchAction {
	
	private ICore m_Core;
	public static final String s_ID = "de.uni_freiburg.informatik.ultimate.gui.LoadSetings";
	public LoadSettingsAction(final IWorkbenchWindow window, final ICore icore) {
		setId(s_ID);
		setText("Load settings");
		setToolTipText("Loads previously saved settings from a file");
		m_Core = icore;
	}
	public void run() {
		m_Core.loadPreferences();
	}
	@Override
	public void dispose() {
		// TODO Auto-generated method stub

	}

}
