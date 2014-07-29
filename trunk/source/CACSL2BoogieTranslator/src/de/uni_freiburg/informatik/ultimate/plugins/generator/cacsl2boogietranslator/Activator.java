/**
 * The activator class controls the plug-in life cycle
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import org.eclipse.core.runtime.Plugin;
import org.osgi.framework.BundleContext;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 03.02.2012
 */
public class Activator extends Plugin {
	/**
	 * The plug-in ID.
	 */
	public static final String s_PLUGIN_ID = CACSL2BoogieTranslator.class.getPackage().getName();
	/**
	 * The plug-in name.
	 */
	public static final String s_PLUGIN_NAME = "CACSL2BoogieTranslator";
	/**
	 * The shared instance.
	 */
	private static Activator m_Plugin;

	/**
	 * The constructor.
	 */
	public Activator() {
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.core.runtime.Plugins#start(org.osgi.framework.BundleContext)
	 */
	@Override
	public void start(BundleContext context) throws Exception {
		super.start(context);
		m_Plugin = this;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.core.runtime.Plugin#stop(org.osgi.framework.BundleContext)
	 */
	@Override
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
