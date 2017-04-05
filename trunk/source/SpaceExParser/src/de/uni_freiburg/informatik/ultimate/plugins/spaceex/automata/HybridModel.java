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

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
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
		mParallelCompositionGenerator = new ParallelCompositionGenerator(mLogger);
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
			final HybridSystem hybsys = createDefaultSystem("system", automata);
			mLogger.debug("hybridsystem created:\n" + hybsys.toString());
			mSystems.put(hybsys.getName(), hybsys);
		} else {
			// create the systems
			systems.forEach((id, comp) -> {
				mLogger.debug("creating hybridsystem for system: " + id);
				final HybridSystem hybsys = mHybridSystemFactory.createHybridSystemFromComponent(id, comp, automata,
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
		mParallelCompositionGenerator = new ParallelCompositionGenerator(mLogger);
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
			final HybridSystem hybsys = createDefaultSystem("system", automata);
			mLogger.debug("hybridsystem created:\n" + hybsys.toString());
			mSystems.put(hybsys.getName(), hybsys);
		} else {
			// create the systems
			systems.forEach((id, comp) -> {
				mLogger.info("creating hybridsystem for system: " + id);
				final HybridSystem hybsys = mHybridSystemFactory.createHybridSystemFromComponent("", comp, automata,
						systems, mPreferenceManager);
				mLogger.info("hybridsystem created:\n" + hybsys.toString());
				mSystems.put(hybsys.getName(), hybsys);
			});
		}
	}
	
	private HybridSystem createDefaultSystem(final String as, final Map<String, ComponentType> automata) {
		assert automata.size() == 1 : "Only one hybrid automaton is possible if no system was defined.";
		final ComponentType automatonComponent = automata.entrySet().iterator().next().getValue();
		final HybridAutomaton automaton =
				mHybridAutomatonFactory.createHybridAutomatonFromComponent(as, automatonComponent, mPreferenceManager);
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
		return mHybridSystemFactory.createHybridSystem(as, globalParams, new HashSet<String>(), globalConstants,
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
		final List<HybridAutomaton> automata = new ArrayList<>(configSystem.getAutomata().values());
		// if there are subsystems, retrieve all of them recursive
		if (!configSystem.getSubSystems().isEmpty()) {
			final List<HybridAutomaton> subsys = getSubSystems(configSystem);
			automata.addAll(subsys);
		}
		// if there is only one automaton, there is nothing to merge.
		if (automata.size() == 1) {
			return automata.iterator().next();
		}
		
		final Map<HybridAutomaton, Location> automataAndInitial = new HashMap<>();
		for (final HybridAutomaton aut : automata) {
			automataAndInitial.put(aut, aut.getInitialLocationForGroup(group != null ? group.getId() : null));
		}
		return mParallelCompositionGenerator.computeParallelCompositionNWay(automataAndInitial);
	}
	
	private List<HybridAutomaton> getSubSystems(final HybridSystem configSystem) {
		final List<HybridAutomaton> automata = new ArrayList<>();
		for (final HybridSystem sys : configSystem.getSubSystems().values()) {
			if (!sys.getSubSystems().isEmpty()) {
				automata.addAll(getSubSystems(sys));
			} else {
				automata.addAll(sys.getAutomata().values());
			}
		}
		return automata;
	}
	
	public HybridSystem getPreferenceSystem(final String system) {
		HybridSystem hybsys;
		if (mSystems.containsKey(system)) {
			hybsys = mSystems.get(system);
		} else if (mSystems.containsKey("system")) {
			hybsys = mSystems.get("system");
		} else {
			throw new IllegalStateException(
					system + " does not exist in the hybrid system, also the default value 'system' does not exist.");
		}
		if (hybsys != null) {
			if (mLogger.isDebugEnabled()) {
				collectAndPrintBinds(hybsys);
			}
			renameSystemAccordingToBinds(hybsys);
		}
		return hybsys;
	}
	
	// TODO: inefficient
	private void renameSystemAccordingToBinds(final HybridSystem hybsys) {
		hybsys.getSubSystems().forEach((id, sys) -> {
			changeSubsystemBinds(sys, hybsys.getBinds());
			renameSystemAccordingToBinds(sys);
		});
		hybsys.getAutomata().forEach((id, aut) -> {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("SYSTEM BINDS: AUTID: " + id + " BINDS: " + hybsys.getBinds().get(id));
				mLogger.debug("############# BEFORE ################");
				mLogger.debug("GLOB CONST: " + aut.getGlobalConstants());
				mLogger.debug("LOC CONST: " + aut.getLocalConstants());
				mLogger.debug("GLOB PARAM: " + aut.getGlobalParameters());
				mLogger.debug("LOC PARAM: " + aut.getLocalParameters());
				mLogger.debug(hybsys.getBinds());
			}
			aut.renameAccordingToBinds(hybsys.getBinds().get(id));
			if (mPreferenceManager != null) {
				aut.renameConstants();
			}
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("############# AFTER ################");
				mLogger.debug("GLOB CONST: " + aut.getGlobalConstants());
				mLogger.debug("LOC CONST: " + aut.getLocalConstants());
				mLogger.debug("GLOB PARAM: " + aut.getGlobalParameters());
				mLogger.debug("LOC PARAM: " + aut.getLocalParameters());
			}
		});
	}
	
	// TODO: Works, but make it easier.
	private void changeSubsystemBinds(final HybridSystem hybsys, final Map<String, Map<String, String>> parentBinds) {
		final Set<Entry<String, String>> parSysbinds = parentBinds.get(hybsys.getName()).entrySet();
		final Set<Entry<String, Map<String, String>>> currSysbinds = hybsys.getBinds().entrySet();
		// iterate over binds of parent
		final Map<String, Map<String, String>> newBinds = new HashMap<>();
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("################# START ###################");
			mLogger.debug("SYS NAME: " + hybsys.getName());
			mLogger.debug("PARENT BINDS: " + parSysbinds);
			mLogger.debug("OLD BINDS: " + currSysbinds);
		}
		for (final Object element : parSysbinds) {
			final Entry<String, String> parEntry = (Entry<String, String>) element;
			final String parKey = parEntry.getKey();
			final String parValue = parEntry.getValue();
			// iterate over binds of current system
			for (final Entry<String, Map<String, String>> curEntry : currSysbinds) {
				final String curKey = curEntry.getKey();
				final Set<Entry<String, String>> curBinds = curEntry.getValue().entrySet();
				// iterate over current system bind maps
				for (final Object element2 : curBinds) {
					final Entry<String, String> curBindEntry = (Entry<String, String>) element2;
					final String curbindKey = curBindEntry.getKey();
					final String curbindValue = curBindEntry.getValue();
					// if current system bind key appears in parent system binds, rename.
					if (parValue.equals(curbindKey)) {
						mLogger.debug("NEW ENTRY:" + "KEY: " + curKey + " VALUE: " + parKey + "=" + curbindValue);
						if (newBinds.containsKey(curKey)) {
							newBinds.get(curKey).put(parKey, curbindValue);
						} else {
							final Map<String, String> tmpmap = new HashMap<>();
							tmpmap.put(parKey, curbindValue);
							newBinds.put(curKey, tmpmap);
						}
					} else {
						if (!curBinds.contains(parValue)) {
							continue;
						}
						if (newBinds.containsKey(curKey)) {
							newBinds.get(curKey).put(curbindKey, curbindValue);
						} else {
							final Map<String, String> tmpmap = new HashMap<>();
							tmpmap.put(curbindKey, curbindValue);
							newBinds.put(curKey, tmpmap);
						}
						mLogger.debug("NEW ENTRY:" + "KEY: " + curKey + " VALUE: " + curbindKey + "=" + curbindValue);
					}
				}
			}
		}
		hybsys.setBinds(newBinds);
		mLogger.debug("NEW BINDS: " + newBinds.toString());
		mLogger.debug("############### END ###############");
	}
	
	private void collectAndPrintBinds(final HybridSystem sys) {
		mLogger.debug("################# SYSTEM BINDS ###################");
		final Map<String, Map<String, String>> binds = sys.getBinds();
		mLogger.debug("SYSNAME: " + sys.getName());
		mLogger.debug("BINDS: " + binds.toString());
		sys.getSubSystems().forEach((id, syst) -> {
			mLogger.debug("################# SUB-SYSTEM BINDS ###################");
			mLogger.debug("ID: " + id);
			mLogger.debug("SUBSYS: " + syst.getBinds().toString());
			if (!syst.getSubSystems().isEmpty()) {
				collectAndPrintBinds(syst);
			}
		});
	}
	
	public Map<String, HybridSystem> getSystems() {
		return mSystems;
	}
}
