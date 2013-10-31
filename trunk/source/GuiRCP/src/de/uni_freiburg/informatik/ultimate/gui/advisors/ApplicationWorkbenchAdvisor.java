package de.uni_freiburg.informatik.ultimate.gui.advisors;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.gui.TrayIconNotifier;
import de.uni_freiburg.informatik.ultimate.gui.UltimateDefaultPerspective;
import de.uni_freiburg.informatik.ultimate.gui.preferencepages.UltimatePreferencePageFactory;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.Platform;
import org.eclipse.swt.widgets.TrayItem;
import org.eclipse.ui.application.IWorkbenchConfigurer;
import org.eclipse.ui.application.IWorkbenchWindowConfigurer;
import org.eclipse.ui.application.WorkbenchAdvisor;
import org.eclipse.ui.application.WorkbenchWindowAdvisor;

/**
 * 
 * @author Ortolf, Dietsch
 * 
 */
public class ApplicationWorkbenchAdvisor extends WorkbenchAdvisor {

	private final Logger mLogger;
	private ICore mCore;
	private ApplicationWorkbenchWindowAdvisor mApplicationWorkbenchWindowAdvisor;
	private TrayIconNotifier mTrayIconNotifier;
	private IController mController;

	public ApplicationWorkbenchAdvisor() {
		mLogger = UltimateServices.getInstance().getControllerLogger();
	}

	public void init(ICore icc, TrayIconNotifier notifier,IController controller){
		mCore = icc;
		mTrayIconNotifier = notifier;
		mController = controller;
		
	}
	
	public WorkbenchWindowAdvisor createWorkbenchWindowAdvisor(
			IWorkbenchWindowConfigurer configurer) {
		mLogger.debug("Requesting WorkbenchWindowAdvisor");
		
		if(mCore == null || mTrayIconNotifier == null){
			throw new IllegalStateException("mCore or mTrayIconNotifier are null; maybe you did not call init()?");
		}
		
		if (mApplicationWorkbenchWindowAdvisor == null) {
			mLogger.debug("Creating WorkbenchWindowAdvisor...");
			mApplicationWorkbenchWindowAdvisor = new ApplicationWorkbenchWindowAdvisor(
					configurer, mCore, mTrayIconNotifier,mController);			
		}
		return mApplicationWorkbenchWindowAdvisor;
	}

	public String getInitialWindowPerspectiveId() {
		return UltimateDefaultPerspective.ID;
	}

	public void initialize(IWorkbenchConfigurer configurer) {
		super.initialize(configurer);
		configurer.setSaveAndRestore(!Platform.inDevelopmentMode());
	}

	public TrayItem getTrayItem() {
		return mApplicationWorkbenchWindowAdvisor.getTrayItem();
	}

	
	
	
	
}
