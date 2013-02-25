package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

import org.eclipse.core.runtime.Plugin;
import org.osgi.framework.BundleContext;
import org.apache.log4j.Logger;


/**
 * The activator class controls the plug-in life cycle
 */
public class Activator extends Plugin {

	// The plug-in ID
	public static final String s_PLUGIN_ID = "BuchiAutomizer";

	// The plug-in name
	public static final String s_PLUGIN_NAME = "BuchiAutomizer";
	// The shared instance
	private static Activator m_Plugin;
	
	private static Logger s_Logger = UltimateServices.getInstance().getLogger(s_PLUGIN_ID);
	
	/**
	 * The constructor
	 */
	public Activator() {
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.core.runtime.Plugins#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		m_Plugin = this;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.core.runtime.Plugin#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext context) throws Exception {
		m_Plugin = null;
		super.stop(context);
	}

	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	public static Activator getDefault() {
		return m_Plugin;
	}

}
