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
	private final BasicIcfg<IcfgLocation> mIcfg;
	private final List<IcfgInternalTransition> mIcfgTransitions;
	private final Map<String, HybridCfgComponent> mCfgComponents;
	private final IPayload mPayload;
	
	public HybridIcfgGenerator(final ILogger logger, final SpaceExPreferenceManager preferenceManager,
			final CfgSmtToolkit smtToolkit) {
		mLogger = logger;
		mSpaceExPreferenceManager = preferenceManager;
		mSmtToolkit = smtToolkit;
		mSmtToolkit.getProcedures().add("root");
		mSmtToolkit.getProcedures().add("error");
		mSmtToolkit.getProcedures().add("varAssignment");
		mSmtToolkit.getProcedures().add("1");
		mSmtToolkit.getProcedures().add("2");
		mIcfg = new BasicIcfg<>("icfg", mSmtToolkit, IcfgLocation.class);
		mPayload = mIcfg.getPayload();
		mIcfgTransitions = new ArrayList<>();
		mCfgComponents = new HashMap<>();
		// create a root + error location;
		final IcfgLocation root = new IcfgLocation("root", "root");
		mCfgComponents.put("root", new HybridCfgComponent("root", root, root, null, null));
		final IcfgLocation error = new IcfgLocation("error", "error");
		mCfgComponents.put("error", new HybridCfgComponent("error", error, error, null, null));
	}
	
	public BasicIcfg<IcfgLocation> createIfcgFromComponents() {
		// root, initial state
		mIcfg.addLocation(mCfgComponents.get("root").getStart(), true, false, false, false, false);
		mCfgComponents.remove("root");
		// error, error state
		mIcfg.addLocation(mCfgComponents.get("error").getStart(), false, true, false, false, false);
		mCfgComponents.remove("error");
		// push the remaining locations into the icfg
		mCfgComponents.forEach((id, comp) -> {
			// start is proc_entry + end is proc_exit
			mIcfg.addOrdinaryLocation(comp.getStart());
			mIcfg.addOrdinaryLocation(comp.getEnd());
			for (final IcfgLocation loc : comp.getLocations()) {
				mIcfg.addOrdinaryLocation(loc);
			}
		});
		return mIcfg;
	}
	
	public void modelToIcfg(final HybridModel model) {
		/*
		 * in order to convert the hybrid model to an ICFG, we have to convert the parallelComposition of the regarded
		 * system.
		 */
		// final String configSystem = mSpaceExPreferenceManager.getSystem();
		final String configSystem = "sys1";
		final Map<String, HybridSystem> systems = model.getSystems();
		final Map<String, HybridAutomaton> mergedAutomata = model.getMergedAutomata();
		HybridAutomaton aut;
		// if the system specified in the config file is present in the models systems
		// else, throw an exception
		mLogger.debug("SYSTEM:");
		mLogger.debug(systems);
		mLogger.debug("");
		mLogger.debug("CONFIG SYSTEM:");
		mLogger.debug(configSystem);
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
					final Collection<HybridAutomaton> autcol = systems.get(configSystem).getAutomata().values();
					final Iterator<HybridAutomaton> it = autcol.iterator();
					aut = it.hasNext() ? it.next() : null;
				}
			}
		} else {
			throw new UnsupportedOperationException("the system specified in the config file: \"" + configSystem
					+ "\" is not part of the hybrid model parsed from file: "
					+ mSpaceExPreferenceManager.getFileName());
		}
		if (aut == null) {
			throw new IllegalStateException("HybridAutomaton aut has not been assigned and is null");
		} else {
			automatonToIcfg(aut);
		}
	}
	
	private void automatonToIcfg(final HybridAutomaton automaton) {
		final Location initialLocation = automaton.getInitialLocation();
		final Map<Integer, Location> locations = automaton.getLocations();
		final List<Transition> transitions = automaton.getTransitions();
		// we can merge all variables into one set.
		final Set<String> variables = automaton.getGlobalParameters();
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
	private void variablesToIcfg(final Set<String> variables) {
		// get initial values of the variable
		final Map<String, List<SignValuePair>> initialVars = mSpaceExPreferenceManager.getInitialVariables();
		// create a location/transition which holds ALL variable assignments.
		final int value;
		for (final String var : variables) {
			// if the variable got an initial value, assign it.
			if (initialVars.containsKey(var)) {
				final List<SignValuePair> init = initialVars.get(var);
				// TODO: convert initial values to a reasonable value or interval
			} else {
				// TODO: assume invariant of initial location.
			}
		}
		// create variable component of the form start ----variable assignment----> end
		final List<IcfgLocation> locations = new ArrayList<>();
		final List<IcfgInternalTransition> transitions = new ArrayList<>();
		final String id = "varAssignment";
		final IcfgLocation start = new IcfgLocation(id + "_start", id);
		final IcfgLocation end = new IcfgLocation(id + "_end", id);
		// TODO: transformula
		final UnmodifiableTransFormula tfStartEnd = null;
		final IcfgInternalTransition startEnd = new IcfgInternalTransition(start, end, mPayload, tfStartEnd);
		start.addOutgoing(startEnd);
		end.addIncoming(startEnd);
		transitions.add(startEnd);
		// new cfgComponent, has to be connected to the root node.
		mCfgComponents.put(id, new HybridCfgComponent(id, start, end, locations, transitions));
		/*
		 * Transition from Root to varAssignment
		 */
		// the source of the transition is the the end of the source CFG component
		final IcfgLocation source = mCfgComponents.get("root").getEnd();
		// the target of the transition is the the start of the target CFG component
		final IcfgLocation target = mCfgComponents.get("varAssignment").getStart();
		// TODO: transformula
		final UnmodifiableTransFormula transFormula = null;
		final IcfgInternalTransition transition = new IcfgInternalTransition(source, target, mPayload, transFormula);
		source.addOutgoing(transition);
		target.addIncoming(transition);
		mIcfgTransitions.add(transition);
	}
	
	/*
	 * Location methods
	 */
	private void locationsToIcfg(final Map<Integer, Location> autLocations) {
		/*
		 * locations consist of Flow and the invariant. -> Startnode (1) -> if/else invariant (2) -> apply flow (3) ->
		 * if/else invariant (4) -> transition/back to (3) if the invariant is injured and no transition can be taken,
		 * go to exit node.
		 */
		for (final Map.Entry<Integer, Location> entry : autLocations.entrySet()) {
			final Integer autid = entry.getKey();
			final Location loc = entry.getValue();
			final List<IcfgInternalTransition> transitions = new ArrayList<>();
			final List<IcfgLocation> locations = new ArrayList<>();
			/*
			 * Locations: Start, End, Flow, InvariantCheck
			 */
			final IcfgLocation start = new IcfgLocation(autid + "_start", autid.toString());
			final IcfgLocation end = new IcfgLocation(autid + "_end", autid.toString());
			final IcfgLocation flow = new IcfgLocation(autid + "_flow", autid.toString());
			locations.add(flow);
			final IcfgLocation invCheck = new IcfgLocation(autid + "_invCheck", autid.toString());
			locations.add(invCheck);
			/*
			 * Transitions from start to Flow/Exit if invariant true, go to flow, else to error loc
			 */
			// TODO: transformula
			final UnmodifiableTransFormula tfStartFlow = null;
			final IcfgInternalTransition startFlow = new IcfgInternalTransition(start, flow, mPayload, tfStartFlow);
			start.addOutgoing(startFlow);
			flow.addIncoming(startFlow);
			transitions.add(startFlow);
			// TODO: transformula
			final UnmodifiableTransFormula tfStartError = null;
			final IcfgInternalTransition startError =
					new IcfgInternalTransition(start, mCfgComponents.get("error").getStart(), mPayload, tfStartError);
			start.addOutgoing(startError);
			mCfgComponents.get("error").getStart().addIncoming(startError);
			transitions.add(startError);
			/*
			 * Transition flow to invCheck
			 */
			// TODO: transformula
			final UnmodifiableTransFormula tfFlowInv = null;
			final IcfgInternalTransition flowInv = new IcfgInternalTransition(flow, invCheck, mPayload, tfFlowInv);
			flow.addOutgoing(flowInv);
			invCheck.addIncoming(flowInv);
			transitions.add(flowInv);
			/*
			 * Transition invCheck to end/exit if invariant true, go to end, else to error loc
			 */
			// invcheck -> end
			// TODO: transformula
			final UnmodifiableTransFormula tfInvEnd = null;
			final IcfgInternalTransition invEnd = new IcfgInternalTransition(invCheck, end, mPayload, tfInvEnd);
			invCheck.addOutgoing(invEnd);
			end.addIncoming(invEnd);
			transitions.add(invEnd);
			// invcheck -> exit
			// TODO: transformula
			final UnmodifiableTransFormula tfInvError = null;
			final IcfgInternalTransition invError =
					new IcfgInternalTransition(invCheck, mCfgComponents.get("error").getStart(), mPayload, tfInvError);
			invCheck.addOutgoing(invError);
			mCfgComponents.get("error").getStart().addIncoming(invError);
			transitions.add(invError);
			/*
			 * Transition End to flow
			 */
			// TODO: transformula
			final UnmodifiableTransFormula tfEndFlow = null;
			final IcfgInternalTransition endFlow = new IcfgInternalTransition(end, flow, mPayload, tfEndFlow);
			end.addOutgoing(endFlow);
			flow.addIncoming(endFlow);
			transitions.add(endFlow);
			// create new cfgComponent
			mCfgComponents.put(autid.toString(),
					new HybridCfgComponent(autid.toString(), start, end, locations, transitions));
		}
	}
	
	/*
	 * Transition methods
	 */
	private void transitionsToIcfg(final List<Transition> transitions) {
		// a transition in a hybrid automaton is simply an edge from one location to another.
		// guard and update can be merged with &&
		transitions.forEach(trans -> {
			// the source of the transition is the the end of the source CFG component
			final IcfgLocation source = mCfgComponents.get(Integer.toString(trans.getSourceId())).getEnd();
			// the target of the transition is the the start of the target CFG component
			final IcfgLocation target = mCfgComponents.get(Integer.toString(trans.getTargetId())).getStart();
			// TODO: transformula
			final UnmodifiableTransFormula transFormula = null;
			final IcfgInternalTransition transition =
					new IcfgInternalTransition(source, target, mPayload, transFormula);
			source.addOutgoing(transition);
			target.addIncoming(transition);
			mIcfgTransitions.add(transition);
		});
	}
}
