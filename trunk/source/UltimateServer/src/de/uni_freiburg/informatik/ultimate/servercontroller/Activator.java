package de.uni_freiburg.informatik.ultimate.servercontroller;

/**
 * The activator class controls the plug-in life cycle.
 */
public final class Activator {

	public static final String PLUGIN_ID = ServerController.class.getPackage().getName();

	public static final String PLUGIN_NAME = "Ultimate Interactive Interface";

	private Activator() {
		// this only stores ID and NAME and is not a RCP activator
	}
}
