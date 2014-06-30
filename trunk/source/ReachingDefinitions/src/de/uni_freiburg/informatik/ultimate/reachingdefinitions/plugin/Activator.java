package de.uni_freiburg.informatik.ultimate.reachingdefinitions.plugin;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.Plugin;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;


/**
 * The activator class controls the plug-in life cycle
 */
public class Activator extends Plugin {

	public static final String PluginName = "ReachingDefinitions";
	public static final String PluginID = PluginName;
	
	public static final Logger getLogger(){
		return UltimateServices.getInstance().getLogger(PluginID);
	}
			
}
