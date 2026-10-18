package de.uni_freiburg.informatik.ultimate.eca.parser;

public final class Activator {
	public static final String PLUGIN_ID = EcaSource.class.getPackage().getName();
	public static final String PLUGIN_NAME = "ECAParser";

	private Activator() {
		// Constants only; this bundle does not need an OSGi lifecycle activator.
	}
}
