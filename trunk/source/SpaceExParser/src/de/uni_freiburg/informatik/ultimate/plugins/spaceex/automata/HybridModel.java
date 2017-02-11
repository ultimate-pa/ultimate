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

import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridAutomatonFactory;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridSystem;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridSystemFactory;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.Location;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.ParallelCompositionGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ComponentType;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.Sspaceex;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences.SpaceExPreferenceGroup;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences.SpaceExPreferenceManager;

/**
 * Class that represents a hybrid model, consisting of multiple concurrently running hybrid automata and some system
 * definitions.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 *
 */
public class HybridModel {
	
	private final ILogger mLogger;
	private final HybridSystemFactory mHybridSystemFactory;
	private final HybridAutomatonFactory mHybridAutomatonFactory;
	private final ParallelCompositionGenerator mParallelCompositionGenerator;
	private Map<String, HybridSystem> mSystems;
	private SpaceExPreferenceManager mPreferenceManager;
	
	/*
	 * This constructor is just for tests.
	 */
	public HybridModel(final Sspaceex root, final ILogger logger) throws Exception {
		mLogger = logger;
		mHybridSystemFactory = new HybridSystemFactory(mLogger);
		mHybridAutomatonFactory = new HybridAutomatonFactory(mLogger);
		mParallelCompositionGenerator = new ParallelCompositionGenerator(mLogger, mPreferenceManager);
		mSystems = new HashMap<>();
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
			final HybridSystem hybsys = createDefaultSystem(automata);
			mLogger.debug("hybridsystem created:\n" + hybsys.toString());
			mSystems.put(hybsys.getName(), hybsys);
		} else {
			// create the systems
			systems.forEach((id, comp) -> {
				mLogger.debug("creating hybridsystem for system: " + id);
				final HybridSystem hybsys = mHybridSystemFactory.createHybridSystemFromComponent(comp, automata,
						systems, mPreferenceManager);
				mLogger.debug("hybridsystem created:\n" + hybsys.toString());
				mSystems.put(hybsys.getName(), hybsys);
			});
		}
	}
	
	/**
	 * v2
	 * 
	 * @param root
	 * @param logger
	 * @param preferenceManager
	 * @throws Exception
	 */
	public HybridModel(final Sspaceex root, final ILogger logger, final SpaceExPreferenceManager preferenceManager)
			throws Exception {
		mLogger = logger;
		mPreferenceManager = preferenceManager;
		mHybridSystemFactory = new HybridSystemFactory(mLogger);
		mHybridAutomatonFactory = new HybridAutomatonFactory(mLogger);
		mParallelCompositionGenerator = new ParallelCompositionGenerator(mLogger, mPreferenceManager);
		mSystems = new HashMap<>();
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
			final HybridSystem hybsys = createDefaultSystem(automata);
			mLogger.debug("hybridsystem created:\n" + hybsys.toString());
			mSystems.put(hybsys.getName(), hybsys);
		} else {
			// create the systems
			systems.forEach((id, comp) -> {
				mLogger.info("creating hybridsystem for system: " + id);
				final HybridSystem hybsys = mHybridSystemFactory.createHybridSystemFromComponent(comp, automata,
						systems, mPreferenceManager);
				mLogger.info("hybridsystem created:\n" + hybsys.toString());
				mSystems.put(hybsys.getName(), hybsys);
			});
		}
	}
	
	private HybridSystem createDefaultSystem(final Map<String, ComponentType> automata) {
		assert automata.size() == 1 : "Only one hybrid automaton is possible if no system was defined.";
		final ComponentType automatonComponent = automata.entrySet().iterator().next().getValue();
		final HybridAutomaton automaton =
				mHybridAutomatonFactory.createHybridAutomatonFromComponent(automatonComponent, mPreferenceManager);
		// set global parameters
		final Set<String> globalParams = automaton.getGlobalParameters().stream()
				.map(g -> new StringBuilder().append("system_").append(g).toString()).collect(Collectors.toSet());
		// set global constants
		final Set<String> globalConstants = automaton.getGlobalConstants().stream()
				.map(gc -> new StringBuilder().append("system_").append(gc).toString()).collect(Collectors.toSet());
		// set labels
		final Set<String> labels = automaton.getLabels().stream()
				.map(l -> new StringBuilder().append("system_").append(l).toString()).collect(Collectors.toSet());
		// set automaton map of the form (name: automaton)
		final Map<String, HybridAutomaton> autMap = new HashMap<>();
		autMap.put(automaton.getName(), automaton);
		// binds
		final Map<String, Map<String, String>> bindsMap = new HashMap<>();
		final Map<String, String> automatonBind = new HashMap<>();
		globalParams.forEach(p -> automatonBind.put(p, p));
		globalConstants.forEach(c -> automatonBind.put(c, c));
		labels.forEach(l -> automatonBind.put(l, l));
		bindsMap.put(automaton.getName(), automatonBind);
		return mHybridSystemFactory.createHybridSystem("system", globalParams, new HashSet<String>(), globalConstants,
				new HashSet<String>(), labels, autMap, new HashMap<String, HybridSystem>(), bindsMap, mLogger);
	}
	
	// function that creates possible parallel compositions for preference groups for the system specified.
	public Map<Integer, HybridAutomaton> calculateParallelCompositionsForGroups(final HybridSystem configSystem) {
		final Map<Integer, HybridAutomaton> groupIdtoMergedAutomaton = new HashMap<>();
		// get preference groups
		final Collection<SpaceExPreferenceGroup> groups = mPreferenceManager.getPreferenceGroups().values();
		// for each group create the parallel composition starting in the groups initial locations.
		for (final SpaceExPreferenceGroup group : groups) {
			final HybridAutomaton merge = mergeAutomata(configSystem, group);
			groupIdtoMergedAutomaton.put(group.getId(), merge);
		}
		return groupIdtoMergedAutomaton;
	}
	
	public HybridAutomaton mergeAutomata(final HybridSystem configSystem, final SpaceExPreferenceGroup group) {
		final Deque<HybridAutomaton> mergeStack = new LinkedList<>();
		final Map<String, String> initLocs = (group == null) ? null : group.getInitialLocations();
		final Map<String, HybridAutomaton> automata = configSystem.getAutomata();
		if (automata.size() == 1) {
			return automata.values().iterator().next();
		}
		mergeStack.addAll(automata.values());
		HybridAutomaton merge = null;
		while (!mergeStack.isEmpty()) {
			HybridAutomaton aut1;
			HybridAutomaton aut2;
			Location init1;
			Location init2;
			if (merge == null) {
				aut1 = mergeStack.pop();
				aut2 = mergeStack.pop();
				init1 = getInitLocation(aut1, initLocs);
				init2 = getInitLocation(aut2, initLocs);
			} else {
				aut1 = merge;
				aut2 = mergeStack.pop();
				init1 = aut1.getInitialLocation();
				init2 = getInitLocation(aut2, initLocs);
			}
			merge = mParallelCompositionGenerator.computeParallelComposition(aut1, aut2, init1, init2);
		}
		return merge;
	}
	
	private Location getInitLocation(final HybridAutomaton aut, final Map<String, String> initLocs) {
		if (initLocs == null) {
			return aut.getInitialLocation();
		}
		final String initLocName = initLocs.get(aut.getName());
		if (aut.getNametoId().containsKey(initLocName)) {
			final int nameToId = aut.getNametoId().get(initLocName);
			return aut.getLocations().get(nameToId);
		} else {
			return aut.getInitialLocation();
		}
	}
	
	public Map<String, HybridSystem> getSystems() {
		return mSystems;
	}
}
