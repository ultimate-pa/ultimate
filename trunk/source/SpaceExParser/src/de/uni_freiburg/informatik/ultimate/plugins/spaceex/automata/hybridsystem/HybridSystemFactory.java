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

package de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ComponentType;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences.SpaceExPreferenceContainer;

/**
 * Factory to create {@link HybridSystem} objects.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public final class HybridSystemFactory {
	
	private final ILogger mLogger;
	
	/**
	 * Default constructor of the {@link HybridSystem} factory.
	 * 
	 * @param logger
	 */
	public HybridSystemFactory(final ILogger logger) {
		mLogger = logger;
	}
	
	/**
	 * Creates a new instance of a hybrid system from a given {@link ComponentType}, obtained from parsing a SpaceEx XML
	 * model description.
	 * 
	 * @param system
	 *            The {@link ComponentType} of the system to create.
	 * @param automata
	 *            The parsed automata.
	 * @param systems
	 *            The parsed systems.
	 * @return A new {@link HybridSystem} instance.
	 */
	public HybridSystem createHybridSystemFromComponent(final String parentSystemName, final ComponentType system,
			final Map<String, ComponentType> automata, final Map<String, ComponentType> systems,
			final SpaceExPreferenceContainer preferenceContainer) {
		return new HybridSystem(parentSystemName, system, automata, systems, mLogger, preferenceContainer);
	}
	
	public HybridSystem createHybridSystem(final String name, final Set<String> globalVariables,
			final Set<String> localVariables, final Set<String> globalConstants, final Set<String> localConstants,
			final Set<String> labels, final Map<String, HybridAutomaton> automata,
			final Map<String, HybridSystem> subsystems, final Map<String, Map<String, String>> binds,
			final ILogger logger) {
		
		return new HybridSystem(name, globalVariables, localVariables, globalConstants, localConstants, labels,
				automata, subsystems, binds, logger);
	}
	
}
