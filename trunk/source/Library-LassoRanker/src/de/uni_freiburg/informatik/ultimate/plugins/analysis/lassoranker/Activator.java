package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import org.osgi.framework.BundleActivator;
import org.osgi.framework.BundleContext;


public class Activator implements BundleActivator {
	/**
	 * The plug-in ID
	 */
	public static final String s_PLUGIN_ID = "LassoRanker";
	
	/**
	 * The plug-in name
	 */
	public static final String s_PLUGIN_NAME = "LassoRanker";
	
	/**
	 * The shared instance
	 */
	private static Activator m_Plugin;
	
	
	private static BundleContext context;

	static BundleContext getContext() {
		return context;
	}

	/**
	 * @see org.osgi.framework.BundleActivator#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext bundleContext) throws Exception {
		Activator.context = bundleContext;
	}

	/**
	 * @see org.osgi.framework.BundleActivator#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext bundleContext) throws Exception {
		Activator.context = null;
	}
	
	/**
	 * @return the shared instance
	 */
	public static Activator getDefault() {
		return m_Plugin;
	}
}
