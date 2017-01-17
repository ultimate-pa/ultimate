/*
 * Copyright (C) 2017 Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.HybridModel;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridSystem;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.Location;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.Transition;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences.SignValuePair;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences.SpaceExPreferenceManager;

/**
 * Class that handles conversion of Hybrid Models/Systems/Automata to an ICFG
 * 
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 *
 */
public class HybridIcfgGenerator {
	
	private final ILogger mLogger;
	private final SpaceExPreferenceManager mSpaceExPreferenceManager;
	private final CfgSmtToolkit mSmtToolkit;
	private BasicIcfg<IcfgLocation> mIcfg;
	private List<IcfgLocation> mIcfgLocations;
	private List<IcfgInternalTransition> mIcfgTransitions;
	private Map<String, HybridCfgComponent> mCfgComponents;
	
	public HybridIcfgGenerator(ILogger logger, SpaceExPreferenceManager preferenceManager, CfgSmtToolkit smtToolkit) {
		mLogger = logger;
		mSpaceExPreferenceManager = preferenceManager;
		mSmtToolkit = smtToolkit;
		mIcfg = new BasicIcfg<>("icfg", mSmtToolkit, IcfgLocation.class);
		mIcfgLocations = new ArrayList<>();
		mIcfgTransitions = new ArrayList<>();
		mCfgComponents = new HashMap<>();
		// create a root + error location;
		IcfgLocation root = new IcfgLocation("root", "root");
		mCfgComponents.put("root", new HybridCfgComponent("root", root, root, null, null));
		IcfgLocation error = new IcfgLocation("error", "error");
		mCfgComponents.put("error", new HybridCfgComponent("error", error, error, null, null));
	}
	
	public BasicIcfg<IcfgLocation> createIfcgFromComponents() {
		return mIcfg;
	}
	
	public void modelToIcfg(HybridModel model) {
		/*
		 * in order to convert the hybrid model to an ICFG, we have to convert the parallelComposition of the regarded
		 * system.
		 */
		String configSystem = mSpaceExPreferenceManager.getSystem();
		Map<String, HybridSystem> systems = model.getSystems();
		Map<String, HybridAutomaton> mergedAutomata = model.getMergedAutomata();
		HybridAutomaton aut;
		// if the system specified in the config file is present in the models systems
		// else, throw an exception
		if (systems.containsKey(configSystem)) {
			// if the system exists, we check if the system has a mergedAutomaton
			// if not it has to be a single automaton (at least it should be)
			if (mergedAutomata.containsKey(configSystem)) {
				aut = mergedAutomata.get(configSystem);
			} else {
				if (systems.get(configSystem).getAutomata().size() != 1) {
					throw new UnsupportedOperationException(
							"The automata of system" + systems.get(configSystem).getName()
									+ " have not been merged or are empty, the size of automata is:"
									+ systems.get(configSystem).getAutomata().size());
				} else {
					// should be a single automaton, thus just get it with an iterator.
					Collection<HybridAutomaton> autcol = systems.get(configSystem).getAutomata().values();
					Iterator<HybridAutomaton> it = autcol.iterator();
					aut = it.hasNext() ? it.next() : null;
				}
			}
		} else {
			throw new UnsupportedOperationException("the system specified in the config file: " + configSystem
					+ " is not part of the hybrid model parsed from file: " + mSpaceExPreferenceManager.getFileName());
		}
		if (aut == null) {
			throw new IllegalStateException("HybridAutomaton aut has not been assigned and is null");
		} else {
			automatonToIcfg(aut);
		}
	}
	
	private void automatonToIcfg(HybridAutomaton automaton) {
		Location initialLocation = automaton.getInitialLocation();
		Map<Integer, Location> locations = automaton.getLocations();
		List<Transition> transitions = automaton.getTransitions();
		// we can merge all variables into one set.
		Set<String> variables = automaton.getGlobalParameters();
		variables.addAll(automaton.getGlobalConstants());
		variables.addAll(automaton.getLocalConstants());
		variables.addAll(automaton.getLocalParameters());
		// ICFG locations + edges for variables
		variablesToIcfg(variables);
		// for locations
		locationsToIcfg(locations);
		// for transitions
		transitionsToIcfg(transitions);
	}
	
	/*
	 * variable methods
	 */
	private void variablesToIcfg(Set<String> variables) {
		// get initial values of the variable
		Map<String, List<SignValuePair>> initialVars = mSpaceExPreferenceManager.getInitialVariables();
		// create a location/transition which holds ALL variable assignments.
		int value;
		for (String var : variables) {
			// if the variable got an initial value, assign it.
			if (initialVars.containsKey(var)) {
				List<SignValuePair> init = initialVars.get(var);
				// TODO: convert initial values to a reasonable value or interval
			} else {
				// TODO: assume invariant of initial location.
			}
		}
		// create variable component of the form start ----variable assignment----> end
		List<IcfgLocation> locations = new ArrayList<>();
		List<IcfgInternalTransition> transitions = new ArrayList<>();
		String id = "varAssignment";
		IcfgLocation start = new IcfgLocation(id + "_start", id);
		locations.add(start);
		IcfgLocation end = new IcfgLocation(id + "_end", id);
		locations.add(end);
		// TODO: Payload + transformula
		IPayload plStartEnd = null;
		UnmodifiableTransFormula tfStartEnd = null;
		IcfgInternalTransition startEnd = new IcfgInternalTransition(start, end, plStartEnd, tfStartEnd);
		transitions.add(startEnd);
		// new cfgComponent, has to be connected to the root node.
		mCfgComponents.put(id, new HybridCfgComponent(id, start, end, locations, transitions));
		/*
		 * Transition from Root to varAssignment
		 */
		// the source of the transition is the the end of the source CFG component
		IcfgLocation source = mCfgComponents.get("root").getEnd();
		// the target of the transition is the the start of the target CFG component
		IcfgLocation target = mCfgComponents.get("varAssignment").getStart();
		// TODO: payload + transformula
		IPayload payload = null;
		UnmodifiableTransFormula transFormula = null;
		IcfgInternalTransition transition = new IcfgInternalTransition(source, target, payload, transFormula);
		mIcfgTransitions.add(transition);
	}
	
	/*
	 * Location methods
	 */
	private void locationsToIcfg(Map<Integer, Location> autLocations) {
		/*
		 * locations consist of Flow and the invariant. -> Startnode (1) -> if/else invariant (2) -> apply flow (3) ->
		 * if/else invariant (4) -> transition/back to (3) if the invariant is injured and no transition can be taken,
		 * go to exit node.
		 */
		for (Map.Entry<Integer, Location> entry : autLocations.entrySet()) {
			Integer autid = entry.getKey();
			Location loc = entry.getValue();
			List<IcfgInternalTransition> transitions = new ArrayList<>();
			List<IcfgLocation> locations = new ArrayList<>();
			/*
			 * Locations: Start, End, Flow, InvariantCheck
			 */
			IcfgLocation start = new IcfgLocation(autid + "_start", autid.toString());
			locations.add(start);
			IcfgLocation end = new IcfgLocation(autid + "_end", autid.toString());
			locations.add(end);
			IcfgLocation flow = new IcfgLocation(autid + "_flow", autid.toString());
			locations.add(flow);
			IcfgLocation invCheck = new IcfgLocation(autid + "_invCheck", autid.toString());
			locations.add(invCheck);
			/*
			 * Transitions from start to Flow/Exit if invariant true, go to flow, else to error loc
			 */
			// TODO: payload + transformula
			IPayload plStartFlow = null;
			UnmodifiableTransFormula tfStartFlow = null;
			IcfgInternalTransition startFlow = new IcfgInternalTransition(start, flow, plStartFlow, tfStartFlow);
			transitions.add(startFlow);
			// TODO: payload + transformula
			IPayload plStartError = null;
			UnmodifiableTransFormula tfStartError = null;
			IcfgInternalTransition startError = new IcfgInternalTransition(start,
					mCfgComponents.get("error").getStart(), plStartError, tfStartError);
			transitions.add(startError);
			/*
			 * Transition flow to invCheck
			 */
			// TODO: payload + transformula
			IPayload plFlowInv = null;
			UnmodifiableTransFormula tfFlowInv = null;
			IcfgInternalTransition flowInv = new IcfgInternalTransition(flow, invCheck, plFlowInv, tfFlowInv);
			transitions.add(flowInv);
			/*
			 * Transition invCheck to end/exit if invariant true, go to end, else to error loc
			 */
			// invcheck -> end
			// TODO: payload + transformula
			IPayload plInvEnd = null;
			UnmodifiableTransFormula tfInvEnd = null;
			IcfgInternalTransition invEnd = new IcfgInternalTransition(invCheck, end, plInvEnd, tfInvEnd);
			transitions.add(invEnd);
			// invcheck -> exit
			// TODO: payload + transformula
			IPayload plInvError = null;
			UnmodifiableTransFormula tfInvError = null;
			IcfgInternalTransition invError = new IcfgInternalTransition(invCheck,
					mCfgComponents.get("error").getStart(), plInvError, tfInvError);
			transitions.add(invError);
			/*
			 * Transition End to flow
			 */
			// TODO: payload + transformula
			IPayload plEndFlow = null;
			UnmodifiableTransFormula tfEndFlow = null;
			IcfgInternalTransition invFlow = new IcfgInternalTransition(flow, invCheck, plEndFlow, tfEndFlow);
			transitions.add(invFlow);
			// create new cfgComponent
			mCfgComponents.put(autid.toString(),
					new HybridCfgComponent(autid.toString(), start, end, locations, transitions));
		}
	}
	
	/*
	 * Transition methods
	 */
	private void transitionsToIcfg(List<Transition> transitions) {
		// a transition in a hybrid automaton is simply an edge from one location to another.
		// guard and update can be merged with &&
		transitions.forEach(trans -> {
			// the source of the transition is the the end of the source CFG component
			IcfgLocation source = mCfgComponents.get(Integer.toString(trans.getSourceId())).getEnd();
			// the target of the transition is the the start of the target CFG component
			IcfgLocation target = mCfgComponents.get(Integer.toString(trans.getTargetId())).getStart();
			// TODO: payload + transformula
			IPayload payload = null;
			UnmodifiableTransFormula transFormula = null;
			IcfgInternalTransition transition = new IcfgInternalTransition(source, target, payload, transFormula);
			mIcfgTransitions.add(transition);
		});
	}
	
}
