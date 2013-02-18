package de.uni_freiburg.informatik.ultimate.gui.advisors;

import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.gui.actions.LoadSettingsAction;
import de.uni_freiburg.informatik.ultimate.gui.actions.LoadSourceFilesAction;
import de.uni_freiburg.informatik.ultimate.gui.actions.ResetAndRedoToolChainAction;
import de.uni_freiburg.informatik.ultimate.gui.actions.ResetAndRedoToolChainNewTCAction;
import de.uni_freiburg.informatik.ultimate.gui.actions.ResetAndRedoToolChainOldTCAction;
import de.uni_freiburg.informatik.ultimate.gui.actions.SaveSettingsAction;

import org.eclipse.jface.action.ICoolBarManager;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;

import org.eclipse.jface.action.ToolBarManager;

import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.actions.ActionFactory;
import org.eclipse.ui.actions.ActionFactory.IWorkbenchAction;
import org.eclipse.ui.application.ActionBarAdvisor;
import org.eclipse.ui.application.IActionBarConfigurer;

/**
 * the class that handles the ations and fills the action bars.
 * 
 * @author Christian Ortolf
 * 
 */
public class ApplicationActionBarAdvisor extends ActionBarAdvisor {

	/**
	 * out interface with the core.
	 */
	private ICore icc;

	/**
	 * standard Exit Action.
	 */
	private IWorkbenchAction exitAction;

	/**
	 * standard aboutAction.
	 */
	private IWorkbenchAction aboutAction;

	/**
	 * standard preference action
	 */
	private IWorkbenchAction preferenceAction;
	/**
	 * our homegrown actions.
	 */
	private IWorkbenchAction /*openPreferencesDialog, openDottyGraphFromFile,*/
			loadSourceFiles;

	private IWorkbenchAction resetAndReRun;
	
	private IWorkbenchAction resetAndReRunNewTC,resetAndReRunOldTC;
	
	private IWorkbenchAction loadSettings,saveSettings;
	/**
	 * standard constructor.
	 * 
	 * @param configurer
	 *            our configurer..
	 * @param isc
	 *            the steerable core for communication and action initilization
	 */
	public ApplicationActionBarAdvisor(IActionBarConfigurer configurer,
			ICore icc) {
		super(configurer);
		this.icc = icc;
	}

	/**
	 * called by Workbench to create our actions.
	 * 
	 * @param window
	 *            the workbench window we are in
	 */
	protected final void makeActions(final IWorkbenchWindow window) {
		exitAction = ActionFactory.QUIT.create(window);
		register(exitAction);
		aboutAction = ActionFactory.ABOUT.create(window);
		register(aboutAction);
		preferenceAction = ActionFactory.PREFERENCES.create(window);
		register(preferenceAction);

		//openPreferencesDialog = new OpenPreferencesDialogAction(window);
		//register(openPreferencesDialog);

		//openDottyGraphFromFile = new OpenDottyGraphFromFileAction(window);
		//register(openDottyGraphFromFile);

		loadSourceFiles = new LoadSourceFilesAction(window, icc);
		register(loadSourceFiles);
		resetAndReRun = new ResetAndRedoToolChainAction(window,icc);
		register(resetAndReRun);
		resetAndReRunNewTC = new ResetAndRedoToolChainNewTCAction(window,icc);
		register(resetAndReRunNewTC);
		resetAndReRunOldTC = new ResetAndRedoToolChainOldTCAction(window,icc);
		register(resetAndReRunOldTC);
		loadSettings = new LoadSettingsAction(window, icc);
		register(loadSettings);
		saveSettings = new SaveSettingsAction(window, icc);
		register(saveSettings);
	}

	/**
	 * called by workbench the menu.
	 * 
	 * @param menuBar
	 */
	protected void fillMenuBar(IMenuManager menuBar) {
		final MenuManager fileMenu = new MenuManager("&File", "file");

		fileMenu.add(loadSourceFiles);
		//fileMenu.add(openDottyGraphFromFile);

//		fileMenu.add(preferenceAction);
		fileMenu.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
		fileMenu.add(new Separator());
		fileMenu.add(exitAction);
		
		MenuManager settingsMenu = new MenuManager("&Settings", "settings");
		settingsMenu.add(preferenceAction);
		settingsMenu.add(new Separator());
		settingsMenu.add(loadSettings);
		settingsMenu.add(saveSettings);

		MenuManager helpMenu = new MenuManager("&Help", "help");
		helpMenu.add(aboutAction);

		menuBar.add(fileMenu);
		menuBar.add(settingsMenu);
		menuBar.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
		menuBar.add(helpMenu);

	}

	protected void fillCoolBar(ICoolBarManager coolBar) {
		IToolBarManager toolBar = new ToolBarManager(coolBar.getStyle());
		coolBar.add(toolBar);

		toolBar.add(loadSourceFiles);
		toolBar.add(new Separator());
		toolBar.add(resetAndReRun);
		toolBar.add(resetAndReRunNewTC);
		toolBar.add(resetAndReRunOldTC);
		toolBar.add(loadSettings);
		toolBar.add(saveSettings);
		//toolBar.add(openDottyGraphFromFile);

		toolBar.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));

	}
}
