package de.uni_freiburg.informatik.ultimate.ep;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.ep.interfaces.IAnalysis;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IOutput;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;

/**
 * Provides the names of Ultimate's OSGi extension points.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public final class ExtensionPoints {
	// /////////////////////////////////////////
	// W A R N I N G //
	// When something is renamed in here, //
	// it MUST also be renamed in //
	// corresponding plugin.xml(s). //
	// /////////////////////////////////////////

	/**
	 * Name of extension point for plugins implementing {@link IController}.
	 */
	public static final String EP_CONTROLLER = "de.uni_freiburg.informatik.ultimate.ep.controller";

	/**
	 * Name of extension point for plugins implementing {@link IGenerator}.
	 */
	public static final String EP_GENERATOR = "de.uni_freiburg.informatik.ultimate.ep.generator";

	/**
	 * Name of extension point for plugins implementing {@link IAnalysis}.
	 */
	public static final String EP_ANALYSIS = "de.uni_freiburg.informatik.ultimate.ep.analysis";

	/**
	 * Name of extension point for plugins implementing {@link IOutput}.
	 */
	public static final String EP_OUTPUT = "de.uni_freiburg.informatik.ultimate.ep.output";

	/**
	 * Name of extension point for plugins implementing {@link ISource}.
	 */
	public static final String EP_SOURCE = "de.uni_freiburg.informatik.ultimate.ep.source";

	/**
	 * Name of extension point for serialization plugins (currently unused).
	 */
	public static final String EP_SERIALIZATION = "de.uni_freiburg.informatik.ultimate.ep.serialization";

	/**
	 * Name of extension point for service plugins.
	 */
	public static final String EP_SERVICE = "de.uni_freiburg.informatik.ultimate.ep.service";

	/**
	 * All extension point names that correspond to plugins (i.e. without the
	 * controller plugin).
	 */
	public static final List<String> PLUGIN_EPS = Collections.unmodifiableList(Arrays.asList(EP_GENERATOR, EP_ANALYSIS,
			EP_OUTPUT, EP_SOURCE, EP_SERVICE));

	/**
	 * Prevent initialization of this class.
	 */
	private ExtensionPoints() {

	}
}
