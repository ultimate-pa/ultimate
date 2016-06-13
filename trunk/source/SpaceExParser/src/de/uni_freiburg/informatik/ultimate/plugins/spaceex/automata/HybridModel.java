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

package de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata;

import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ComponentType;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.Sspaceex;

/**
 * Class that represents a hybrid model, consisting of multiple concurrently running hybrid automata and some system
 * definitions.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class HybridModel {

	private final ILogger mLogger;

	public HybridModel(Sspaceex root, ILogger logger) {
		mLogger = logger;

		final Map<String, ComponentType> automata = root.getComponent().stream().filter(c -> c.getBind().isEmpty())
		        .collect(Collectors.toMap(ComponentType::getId, Function.identity(), (oldEntry, newEntry) -> {
			        mLogger.warn("A hybrid automaton with name " + oldEntry.getId()
		                    + " already exists. Overwriting with new one.");
			        return newEntry;
		        }));

		final Map<String, ComponentType> systems = root.getComponent().stream().filter(c -> !c.getBind().isEmpty())
		        .collect(Collectors.toMap(ComponentType::getId, Function.identity(), (oldEntry, newEntry) -> {
			        mLogger.warn("A hybrid system with name " + oldEntry.getId()
		                    + " already exists. Overwriting with new one.");
			        return newEntry;
		        }));

		if (systems.size() == 0 && automata.size() > 1) {
			throw new UnsupportedOperationException(
			        "If no hybrid system is specified, only one automaton is allowed to exist in the model.");
		}

		if (systems.size() == 0) {
			createDefaultSystem(automata);
		} else {
			// TODO for the time being, we use the first defined system as default system. Read system name from config
			// file in the future.
			new HybridSystem(systems.values().stream().collect(Collectors.toList()).get(0), automata, systems, mLogger);
		}
	}

	private void createDefaultSystem(Map<String, ComponentType> automata) {
		// TODO Fill.
	}
}
