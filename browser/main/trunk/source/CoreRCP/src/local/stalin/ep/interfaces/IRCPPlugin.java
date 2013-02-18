package local.stalin.ep.interfaces;

/**
 * @author partial
 *
 */
public interface IRCPPlugin {
	/**
	 * if any kind of initialisation should go here
	 * method is called by core after the plugin is loaded
	 */
	int init(Object params);
	
	/**
	 * 
	 * @return a human readable Name for the plugin.
	 */
	String getName();
	
	/**
	 * Method which returns ID of the Plugin.
	 * @return String containing Plugin ID
	 */
	String getPluginID();
}
