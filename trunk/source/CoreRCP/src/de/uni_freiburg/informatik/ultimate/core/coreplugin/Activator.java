package de.uni_freiburg.informatik.ultimate.core.coreplugin;

import org.eclipse.core.runtime.Plugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle.
 */
public class Activator extends Plugin {

	/**
	 * Unique Plugin ID. Similar to the one in plugin.xml
	 */
	public static final String s_PLUGIN_ID = "UltimateCore";

	/**
	 * String s_PLUGIN_NAME
	 */
	public static String s_PLUGIN_NAME = "UltimateCore";

	/**
	 * The shared instance.
	 */
	private static Activator s_Plugin;

	/**
	 * The constructor. Does nothing important.
	 */
	public Activator() {
	}

	/**
	 * Method is called when plugin is started.
	 * 
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
	 * @param context
	 *            The Context in which plugin is started.
	 * @throws Exception
	 *             Can throw any exception
	 */
	public final void start(final BundleContext context) throws Exception {
		super.start(context);
		s_Plugin = this;
	}

	/**
	 * Method is called when plugin is stopped.
	 * 
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
	 * @param context
	 *            The Context in which plugin is stopped.
	 * @throws Exception
	 *             Can throw any exception
	 */
	public final void stop(final BundleContext context) throws Exception {
		s_Plugin = null;
		super.stop(context);
		System.out.println("Closed successfully");
	}

	/**
	 * Returns the shared instance.
	 * 
	 * @return the shared instance
	 */
	public static Activator getDefault() {
		return s_Plugin;
	}

}
