package local.stalin.gui.actions;

import local.stalin.ep.interfaces.ICore;

import org.eclipse.jface.action.Action;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.actions.ActionFactory.IWorkbenchAction;

public class SaveSettingsAction extends Action implements IWorkbenchAction {

	private ICore m_Core;
	public static final String s_ID = "local.stalin.gui.SaveSetings";
	public SaveSettingsAction(final IWorkbenchWindow window, final ICore icore) {
		setId(s_ID);
		setText("Save settings");
		setToolTipText("Saves current settings to a file");
		m_Core = icore;
	}
	public void run() {
		m_Core.savePreferences();
	}
	@Override
	public void dispose() {}

}
