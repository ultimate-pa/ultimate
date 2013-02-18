package local.stalin.plugins.output.jungvisualization;

import org.eclipse.core.runtime.Plugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle. It seems to be neccessary for a seamless rcp integration. 
 * This is an automatically generated class!
 *
 * @author lena
 *
 */
public class Activator extends Plugin {

	public static final String PLUGIN_ID = "local.stalin.plugins.output.jungvisualization";
	
	// The shared instance
	private static Activator plugin;
	
	/**
	 * The constructor.
	 */
	public Activator() {
		plugin = this;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.core.runtime.Plugin#start(org.osgi.framework.BundleContext)
	 */
	@Override
	public void start(BundleContext context) throws Exception {
		super.start(context);
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.core.runtime.Plugin#stop(org.osgi.framework.BundleContext)
	 */
	@Override
	public void stop(BundleContext context) throws Exception {
		super.stop(context);
		plugin = null;
	}
	
	/**
	 * Returns the shared instance of plugin.
	 * @return The shared instance of plugin.
	 */
	public static Activator getDefault() {
		return plugin;
	}
}
