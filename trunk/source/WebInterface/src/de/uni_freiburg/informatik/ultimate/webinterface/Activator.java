package de.uni_freiburg.informatik.ultimate.webinterface;

import org.osgi.framework.Bundle;
import org.osgi.framework.BundleActivator;
import org.osgi.framework.BundleContext;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 25.03.2012
 */
public class Activator implements BundleActivator {
	/**
	 * The ServiceTracker to hold.
	 */
	private HttpTracker httpServiceTracker;
	/**
	 * the bundle instance.
	 */
	private static Bundle plugin;
	
	@Override
	public void start(BundleContext context) throws Exception {
		httpServiceTracker = new HttpTracker(context);
		httpServiceTracker.open();
		plugin = context.getBundle();
	}

	@Override
	public void stop(BundleContext context) throws Exception {
		httpServiceTracker.close();
		httpServiceTracker = null;
		plugin = null;
	}
	
	/**
	 * Returns the instance of the bundle.
	 * @return the bundle instance
	 */
	public static Bundle getDefault() {
		return plugin;
	}
}
