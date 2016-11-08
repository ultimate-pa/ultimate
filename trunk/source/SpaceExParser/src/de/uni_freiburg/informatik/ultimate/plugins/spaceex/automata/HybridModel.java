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
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridAutomatonFactory;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridSystem;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridSystemFactory;
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
	private final HybridSystemFactory mHybridSystemFactory;
	private final HybridAutomatonFactory mHybridAutomatonFactory;
	private final HybridSystem mRootSystem;

	public HybridModel(final Sspaceex root, final ILogger logger) {
		mLogger = logger;

		mHybridSystemFactory = new HybridSystemFactory(mLogger);
		mHybridAutomatonFactory = new HybridAutomatonFactory(mLogger);

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

		if (systems.isEmpty() && automata.size() > 1) {
			throw new UnsupportedOperationException(
			        "If no hybrid system is specified, only one automaton is allowed to exist in the model.");
		}

		if (systems.isEmpty()) {
			mRootSystem = createDefaultSystem(automata);
		} else {
			// TODO for the time being, we use the first defined system as default system. Read system name from config
			// file in the future.
			final ComponentType firstSystem = systems.values().stream().collect(Collectors.toList()).get(0);
			mRootSystem = mHybridSystemFactory.createHybridSystemFromComponent(firstSystem, automata, systems);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(mRootSystem);
			}
		}
	}

	private HybridSystem createDefaultSystem(final Map<String, ComponentType> automata) {
		assert automata.size() == 1 : "Only one hybrid automaton is possible if no system was defined.";

		final ComponentType automatonComponent = automata.entrySet().iterator().next().getValue();

		final HybridAutomaton automaton = mHybridAutomatonFactory
		        .createHybridAutomatonFromComponent(automatonComponent);

		final Set<String> globalParams = automaton.getGlobalParameters().stream()
		        .map(g -> new StringBuilder().append("system_").append(g).toString()).collect(Collectors.toSet());
		final Set<String> globalConstants = automaton.getGlobalConstants().stream()
		        .map(gc -> new StringBuilder().append("system_").append(gc).toString()).collect(Collectors.toSet());
		final Set<String> labels = automaton.getLabels().stream()
		        .map(l -> new StringBuilder().append("system_").append(l).toString()).collect(Collectors.toSet());

		final Map<String, HybridAutomaton> autMap = new HashMap<>();
		autMap.put(automaton.getName(), automaton);

		final Map<String, Map<String, String>> bindsMap = new HashMap<>();
		final Map<String, String> automatonBind = new HashMap<>();

		globalParams.forEach(p -> automatonBind.put(p, p));
		globalConstants.forEach(c -> automatonBind.put(c, c));
		labels.forEach(l -> automatonBind.put(l, l));
		
		bindsMap.put(automaton.getName(), automatonBind);
		
		
		return mHybridSystemFactory.createHybridSystem("system", globalParams, new HashSet<String>(), globalConstants,
		        new HashSet<String>(), labels, autMap, new HashMap<String, HybridSystem>(), bindsMap, mLogger);
	}
}
