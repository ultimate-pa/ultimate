/*
 * Copyright (C) 2007-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2007-2015 Robert Jakob
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.ep;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.IAnalysis;
import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.IGenerator;
import de.uni_freiburg.informatik.ultimate.core.model.IOutput;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;

/**
 * Provides the names of Ultimate's OSGi extension points.
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public final class UltimateExtensionPoints {
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
	 * All extension point names that correspond to plugins (i.e. without the controller plugin).
	 */
	public static final List<String> PLUGIN_EPS =
			Collections.unmodifiableList(Arrays.asList(EP_GENERATOR, EP_ANALYSIS, EP_OUTPUT, EP_SOURCE, EP_SERVICE));

	/**
	 * Prevent initialization of this class.
	 */
	private UltimateExtensionPoints() {
		// utility class
	}
}
