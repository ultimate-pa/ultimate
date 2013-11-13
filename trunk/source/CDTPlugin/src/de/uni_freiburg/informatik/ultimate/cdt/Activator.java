/**
 * The activator class controls the plug-in life cycle
 */
package de.uni_freiburg.informatik.ultimate.cdt;

import org.eclipse.cdt.codan.core.CodanCorePlugin;
import org.eclipse.cdt.codan.core.model.IProblemReporter;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore.Ultimate_Mode;

/**
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @date 30.01.2012
 */
public class Activator extends AbstractUIPlugin {

	/**
	 * The plug-in ID.
	 */
	public static final String PLUGIN_ID = "CDTPlugin";
	/**
	 * The shared instance
	 */
	private static Activator plugin;
	/**
	 * The used application (holds the reference to ultimate).
	 */
	public static UltimateCore app;

	/**
	 * The constructor
	 */
	public Activator() {
		// UltimateServices.createInstance(app); //FIXME : will crash ultimate
		if (UltimateServices.getInstance() == null) {
			app = new UltimateCore(Ultimate_Mode.EXTERNAL_EXECUTION);
			UltimateServices.createInstance(app);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext
	 * )
	 */
	@Override
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
		// we delete old Codan-Results on Plugin-Startup
		// --> this good because the results of Ultimate are not persisted
		deleteAllProblems();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext
	 * )
	 */
	@Override
	public void stop(BundleContext context) throws Exception {
		plugin = null;
		super.stop(context);
	}

	/**
	 * This method deletes all Codan Markers found during the last session
	 */
	private void deleteAllProblems() {
		try {
			ResourcesPlugin
					.getWorkspace()
					.getRoot()
					.deleteMarkers(
							IProblemReporter.GENERIC_CODE_ANALYSIS_MARKER_TYPE,
							true, IResource.DEPTH_INFINITE);
		} catch (CoreException e) {
			CodanCorePlugin.log(e);
		}
	}

	/**
	 * Returns the shared instance
	 * 
	 * @return the shared instance
	 */
	public static Activator getDefault() {
		return plugin;
	}
}
