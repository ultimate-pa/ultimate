/*
 * Copyright (C) 2016 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences.SpaceExPreferenceContainer;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences.SpaceExPreferenceGroup;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.util.HybridTranslatorConstants;

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
	private SpaceExPreferenceContainer mPreferenceContainer;
	
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
						systems, mPreferenceContainer);
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
	public HybridModel(final Sspaceex root, final ILogger logger, final SpaceExPreferenceContainer preferenceContainer)
			throws Exception {
		mLogger = logger;
		mPreferenceContainer = preferenceContainer;
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
						systems, mPreferenceContainer);
				mLogger.info("hybridsystem created:\n" + hybsys.toString());
				mSystems.put(hybsys.getName(), hybsys);
			});
		}
	}
	
	private HybridSystem createDefaultSystem(final String as, final Map<String, ComponentType> automata) {
		assert automata.size() == 1 : "Only one hybrid automaton is possible if no system was defined.";
		final ComponentType automatonComponent = automata.entrySet().iterator().next().getValue();
		final HybridAutomaton automaton = mHybridAutomatonFactory.createHybridAutomatonFromComponent(as,
				"defaultSystem", automatonComponent, mPreferenceContainer);
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
		final Collection<SpaceExPreferenceGroup> groups = mPreferenceContainer.getPreferenceGroups().values();
		
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
			final List<HybridAutomaton> subsys = getSubSystemAutomata(configSystem);
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
	
	private List<HybridAutomaton> getSubSystemAutomata(final HybridSystem configSystem) {
		final List<HybridAutomaton> automata = new ArrayList<>();
		for (final HybridSystem sys : configSystem.getSubSystems().values()) {
			if (!sys.getSubSystems().isEmpty()) {
				automata.addAll(getSubSystemAutomata(sys));
			} else {
				automata.addAll(sys.getAutomata().values());
			}
		}
		return automata;
	}
	
	/**
	 * Returns a @HybridSystem with the given name, if it exists.
	 * 
	 * @param systemName
	 * @return
	 */
	public HybridSystem getSystemByName(final String systemName) {
		HybridSystem hybsys;
		if (mSystems.containsKey(systemName)) {
			hybsys = mSystems.get(systemName);
		} else if (mSystems.containsKey(HybridTranslatorConstants.DEFAULT_SYSTEM_NAME)) {
			hybsys = mSystems.get(HybridTranslatorConstants.DEFAULT_SYSTEM_NAME);
		} else {
			throw new IllegalStateException(systemName
					+ " does not exist in the hybrid system, also the default value 'system' does not exist.");
		}
		if (hybsys != null) {
			if (mLogger.isDebugEnabled()) {
				collectAndPrintBinds(hybsys);
			}
			renameSystemAccordingToBinds(hybsys);
			renameVariables(hybsys);
		}
		return hybsys;
	}
	
	private void renameVariables(final HybridSystem hybsys) {
		hybsys.getAutomata().forEach((id, aut) -> {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("RENAME VARS");
				mLogger.debug("############# BEFORE ################");
				mLogger.debug("GLOB CONST: " + aut.getGlobalConstants());
				mLogger.debug("LOC CONST: " + aut.getLocalConstants());
				mLogger.debug("GLOB PARAM: " + aut.getGlobalParameters());
				mLogger.debug("LOC PARAM: " + aut.getLocalParameters());
				mLogger.debug(hybsys.getBinds());
			}
			aut.renameReplacedVariables();
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("############# AFTER ################");
				mLogger.debug("GLOB CONST: " + aut.getGlobalConstants());
				mLogger.debug("LOC CONST: " + aut.getLocalConstants());
				mLogger.debug("GLOB PARAM: " + aut.getGlobalParameters());
				mLogger.debug("LOC PARAM: " + aut.getLocalParameters());
			}
		});
		
		hybsys.getSubSystems().forEach((id, sys) -> {
			renameVariables(sys);
		});
	}
	
	private void renameSystemAccordingToBinds(final HybridSystem hybsys) {
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
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("############# AFTER ################");
				mLogger.debug("GLOB CONST: " + aut.getGlobalConstants());
				mLogger.debug("LOC CONST: " + aut.getLocalConstants());
				mLogger.debug("GLOB PARAM: " + aut.getGlobalParameters());
				mLogger.debug("LOC PARAM: " + aut.getLocalParameters());
			}
		});
		
		hybsys.getSubSystems().forEach((id, sys) -> {
			changeSubsystemBinds(sys, hybsys.getBinds());
			renameSystemAccordingToBinds(sys);
		});
	}
	
	private void changeSubsystemBinds(final HybridSystem hybsys, final Map<String, Map<String, String>> parentBinds) {
		// copy binds
		final Map<String, Map<String, String>> localbinds = hybsys.getBinds().entrySet().stream()
				.collect(Collectors.toMap(e -> e.getKey(), e -> new HashMap<>(e.getValue())));
		
		// parent binds for the current hybrid system.
		final Map<String, String> globalbinds =
				parentBinds.containsKey(hybsys.getName()) ? parentBinds.get(hybsys.getName()) : null;
		
		mLogger.debug("################ START #################");
		mLogger.debug("LOCALBINDS: " + localbinds);
		mLogger.debug("GLOBALBINDS: " + globalbinds);
		
		if (globalbinds != null && localbinds != null) {
			localbinds.forEach((id, binds) -> {
				mLogger.debug("ID " + id);
				mLogger.debug("BINDS" + binds);
				binds.forEach((subGlobal, subLocal) -> {
					globalbinds.forEach((parGlobal, parLocal) -> {
						if (parLocal.equals(subGlobal) && !parGlobal.equals(subGlobal)) {
							hybsys.getBinds().get(id).put(parGlobal, subLocal);
							hybsys.getBinds().get(id).remove(subGlobal);
						}
					});
				});
			});
		}
		
		mLogger.debug("LOCALBINDS: " + hybsys.getBinds());
		mLogger.debug("GLOBALBINDS: " + globalbinds);
		mLogger.debug("################ END #################");
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
