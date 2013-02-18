package de.uni_freiburg.informatik.ultimate.plugins.generator.automatalibraryrandomizedtests;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

import org.eclipse.core.runtime.Plugin;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.preferences.ScopedPreferenceStore;
import org.osgi.framework.BundleContext;
import org.apache.log4j.Logger;


/**
 * The activator class controls the plug-in life cycle
 */
public class Activator extends Plugin {

	// The plug-in ID
	public static final String s_PLUGIN_ID = "AutomataLibraryRandomizedTests";

	// The plug-in name
	public static final String s_PLUGIN_NAME = "AutomataLibraryRandomizedTests";
	// The shared instance
	private static Activator m_Plugin;
	
	private static ScopedPreferenceStore preferences; 
	
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
		preferences = new ScopedPreferenceStore(new ConfigurationScope(),Activator.s_PLUGIN_ID);
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
	
	public IPreferenceStore getPreferenceStore() {
		return preferences;
	}

}
