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

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ComponentType;

/**
 * Representation of a hybrid system that contains of multiple hybrid automata.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class HybridSystem {

	private final ILogger mLogger;
	private final Map<String, HybridAutomaton> mAutomata;
	private final Map<String, HybridSystem> mSubSystems;

	protected HybridSystem(ComponentType system, Map<String, ComponentType> automata,
	        Map<String, ComponentType> systems, ILogger logger) {
		assert !system.getBind().isEmpty() : "System must contain binds";

		mLogger = logger;
		mAutomata = new HashMap<>();
		mSubSystems = new HashMap<>();

		system.getBind().stream().forEach(b -> {
			final String comp = b.getComponent();
			if (systems.containsKey(comp)) {
				mSubSystems.put(b.getAs(), new HybridSystem(systems.get(comp), automata, systems, mLogger));
			} else if (automata.containsKey(comp)) {
				mAutomata.put(b.getAs(), new HybridAutomaton(automata.get(comp), mLogger));
			} else {
				throw new UnsupportedOperationException(
		                "The component with name " + comp + " is neither a system nor an automaton component.");
			}
		});
	}

	private void addHybridAutomaton(ComponentType component) {
		final HybridAutomaton newAutomaton = new HybridAutomaton(component, mLogger);
		final HybridAutomaton old = mAutomata.put(component.getId(), newAutomaton);
		if (old != null) {
			mLogger.warn("A hybrid automaton with name " + old.getName() + " already existed and was replaced.");
		}

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Added hybrid automaton " + newAutomaton);
		}
	}
}
