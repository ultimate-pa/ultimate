package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2;

import org.eclipse.core.runtime.Plugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class AIActivator extends Plugin {

	// The plug-in ID
	public static final String s_PLUGIN_ID = AbstractInterpretation.class
			.getPackage().getName();

	// The plug-in name
	public static final String s_PLUGIN_NAME = "AbstractInterpretationMk2";

	// The shared instance
	private static AIActivator m_Plugin;

	/**
	 * The constructor
	 */
	public AIActivator() {

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext
	 * )
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		m_Plugin = this;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext
	 * )
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
	public static AIActivator getDefault() {
		return m_Plugin;
	}
}
