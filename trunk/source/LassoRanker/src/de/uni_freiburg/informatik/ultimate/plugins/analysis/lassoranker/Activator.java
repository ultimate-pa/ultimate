package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import org.eclipse.core.runtime.Plugin;
import org.osgi.framework.BundleContext;



/**
 * The activator class controls the plug-in life cycle
 */
public class Activator extends Plugin {
	/**
	 * The plug-in ID
	 */
	public static final String s_PLUGIN_ID = LassoRanker.class.getPackage().getName();
	
	/**
	 * The plug-in name
	 */
	public static final String s_PLUGIN_NAME = "LassoRanker";
	
	/**
	 * The shared instance
	 */
	private static Activator m_Plugin;
	
	/**
	 * @see org.eclipse.core.runtime.Plugins#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		m_Plugin = this;
	}

	/**
	 * @see org.eclipse.core.runtime.Plugin#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext context) throws Exception {
		m_Plugin = null;
		super.stop(context);
	}

	/**
	 * @return the shared instance
	 */
	public static Activator getDefault() {
		return m_Plugin;
	}
}