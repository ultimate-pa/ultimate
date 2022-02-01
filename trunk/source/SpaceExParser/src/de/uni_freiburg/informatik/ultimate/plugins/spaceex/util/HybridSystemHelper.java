/*
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE SpaceExParser plug-in.
 * 
 * The ULTIMATE SpaceExParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE SpaceExParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SpaceExParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SpaceExParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE SpaceExParser plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.spaceex.util;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ParamType;

/**
 * Helper methods for dealing with hybrid systems, hybrid automata and so on.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class HybridSystemHelper {

	public static void addParameter(ParamType param, Collection<String> localParameters,
	        Collection<String> globalParameters, Collection<String> localConstants, Collection<String> globalConstants,
	        Collection<String> labels, ILogger logger) {
		final String name = param.getName();

		switch (param.getType()) {
		case "real":
			switch (param.getDynamics()) {
			case "any":
				if (param.isLocal()) {
					addParameterToSet(name, localParameters, logger);
				} else {
					addParameterToSet(name, globalParameters, logger);
				}
				break;
			case "const":
				if (param.isLocal()) {
					addParameterToSet(name, localConstants, logger);
				} else {
					addParameterToSet(name, globalConstants, logger);
				}
				break;
			default:
				throw new UnsupportedOperationException("The parameter type " + param.getType() + " is not supported.");
			}
			break;
		case "label":
			addParameterToSet(name, labels, logger);
			break;
		default:
			throw new IllegalArgumentException("The parameter type " + param.getType() + " is unknown.");
		}
	}

	private static void addParameterToSet(final String name, Collection<String> collection, ILogger logger) {
		if (!collection.add(name)) {
			logger.warn("The variable with name " + name + " is already present in the set.");
		}
		
		if (logger.isDebugEnabled()) {
			logger.debug("Added parameter " + name);
		}
	}

}
