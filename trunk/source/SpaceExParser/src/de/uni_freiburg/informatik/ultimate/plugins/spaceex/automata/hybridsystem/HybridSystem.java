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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.BindType;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ComponentType;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.util.HybridSystemHelper;

/**
 * Representation of a hybrid system that contains of multiple hybrid automata.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class HybridSystem {

	private final ILogger mLogger;
	private final String mName;
	private final Map<String, HybridAutomaton> mAutomata;
	private final Map<String, HybridSystem> mSubSystems;
	private final Set<String> mLocalParameters;
	private final Set<String> mGlobalParameters;
	private final Set<String> mLocalConstants;
	private final Set<String> mGlobalConstants;
	private final Set<String> mLabels;
	private final Map<String, Map<String, String>> mBinds;

	protected HybridSystem(ComponentType system, Map<String, ComponentType> automata,
	        Map<String, ComponentType> systems, ILogger logger) {
		assert !system.getBind().isEmpty() : "System must contain binds";

		mLogger = logger;
		mName = system.getId();
		mAutomata = new HashMap<>();
		mSubSystems = new HashMap<>();
		mLocalParameters = new HashSet<>();
		mGlobalParameters = new HashSet<>();
		mLocalConstants = new HashSet<>();
		mGlobalConstants = new HashSet<>();
		mLabels = new HashSet<>();
		mBinds = new HashMap<>();

		system.getParam().forEach(p -> HybridSystemHelper.addParameter(p, mLocalParameters, mGlobalParameters,
		        mLocalConstants, mGlobalConstants, mLabels, mLogger));

		system.getBind().stream().forEach(b -> {
			final String comp = b.getComponent();
			if (systems.containsKey(comp)) {
				final HybridSystem old = mSubSystems.put(b.getAs(),
		                new HybridSystem(systems.get(comp), automata, systems, mLogger));
				if (old != null) {
					mLogger.warn("A hybrid system with name " + b.getAs() + " already existed and was replaced.");
				}
			} else if (automata.containsKey(comp)) {
				final HybridAutomaton old = mAutomata.put(b.getAs(), new HybridAutomaton(automata.get(comp), mLogger));
				if (old != null) {
					mLogger.warn("A hybrid automaton with name " + b.getAs() + " already existed and was replaced.");
				}
			} else {
				throw new UnsupportedOperationException(
		                "The component with name " + comp + " is neither a system nor an automaton component.");
			}

			final Map<String, String> binds = b.getMap().stream()
		            .collect(Collectors.toMap(BindType.Map::getValue, BindType.Map::getKey));
			mBinds.put(comp, binds);
		});
		
	}

	protected HybridSystem(final String name, final Set<String> globalVariables, final Set<String> localVariables,
	        final Set<String> globalConstants, final Set<String> localConstants, final Set<String> labels,
	        final Map<String, HybridAutomaton> automata, final Map<String, HybridSystem> subsystems,
	        final Map<String, Map<String, String>> binds, final ILogger logger) {
		mLogger = logger;
		mName = name;
		mAutomata = automata;
		mSubSystems = subsystems;
		mLocalParameters = localVariables;
		mGlobalParameters = globalVariables;
		mLocalConstants = localConstants;
		mGlobalConstants = globalConstants;
		mLabels = labels;
		mBinds = binds;
		// TODO Add bind.
	}
	
	public Map<String, HybridAutomaton> getAutomata(){
		return mAutomata;
	}
	
	public String getName(){
		return mName;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		final String indent = "   ";
		sb.append("System ").append(mName).append(":\n");
		sb.append(indent).append("Parameters (global):\n");
		mGlobalParameters.forEach(p -> sb.append(indent).append(indent).append("* ").append(p).append("\n"));
		sb.append(indent).append("Parameters (local):\n");
		mLocalParameters.forEach(p -> sb.append(indent).append(indent).append("* ").append(p).append("\n"));
		sb.append(indent).append("Constants (global):\n");
		mGlobalConstants.forEach(p -> sb.append(indent).append(indent).append("* ").append(p).append("\n"));
		sb.append(indent).append("Constants (local):\n");
		mLocalConstants.forEach(p -> sb.append(indent).append(indent).append("* ").append(p).append("\n"));
		sb.append(indent).append("Labels:\n");
		mLabels.forEach(p -> sb.append(indent).append(indent).append("* ").append(p).append("\n"));
		sb.append(indent).append("Automata:\n");
		mAutomata.forEach((name, aut) -> sb.append(indent).append("Automaton ").append(name).append(":\n")
				.append(indent).append(indent).append(aut).append("\n"));
		sb.append(indent).append("Subsystems:\n");
		mSubSystems.forEach((name, sys) -> sb.append(indent).append(indent).append("* System ").append(name + "\n"));		
		sb.append(indent).append("binds:\n");
		mBinds.forEach((k,v)->{
			sb.append(indent + "automata: " + k + " bind: " + v + "\n");
		});
		return sb.toString();
	}
}
