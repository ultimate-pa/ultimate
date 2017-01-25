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
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.Payload;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.HybridAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.Location;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.hybridsystem.Transition;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg.HybridTermBuilder.BuildScenario;
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
	private final Map<String, HybridCfgComponent> mCfgComponents;
	private final IPayload mPayload;
	private final String mProcedure = "MAIN";
	private final BoogieASTNode mBoogieASTNode;
	private final HybridVariableManager mVariableManager;
	
	public HybridIcfgGenerator(final ILogger logger, final SpaceExPreferenceManager preferenceManager,
			final CfgSmtToolkit smtToolkit) {
		mLogger = logger;
		mSpaceExPreferenceManager = preferenceManager;
		mSmtToolkit = smtToolkit;
		mVariableManager = new HybridVariableManager(smtToolkit.getManagedScript());
		final ILocation dummyLoc = new DummyLocation(preferenceManager.getFileName());
		mPayload = new Payload(dummyLoc);
		mCfgComponents = new HashMap<>();
		mBoogieASTNode = new BoogieASTNode(dummyLoc);
		// create a root + error location;
		final BoogieIcfgLocation root = new BoogieIcfgLocation("root", mProcedure, false, mBoogieASTNode);
		mCfgComponents.put("root",
				new HybridCfgComponent("root", root, root, Collections.EMPTY_LIST, Collections.EMPTY_LIST));
		final BoogieIcfgLocation error = new BoogieIcfgLocation("error", mProcedure, true, mBoogieASTNode);
		mCfgComponents.put("error",
				new HybridCfgComponent("error", error, error, Collections.EMPTY_LIST, Collections.EMPTY_LIST));
	}
	
	public BasicIcfg<BoogieIcfgLocation> createIfcgFromComponents(HybridAutomaton automaton) {
		modelToIcfg(automaton);
		final BasicIcfg<BoogieIcfgLocation> icfg = new BasicIcfg<>("testicfg", mSmtToolkit, BoogieIcfgLocation.class);
		mCfgComponents.forEach((key, value) -> {
			mLogger.debug("ID:" + key + ", Component:" + value.toString());
		});
		// root, initial state
		icfg.addLocation(mCfgComponents.get("root").getStart(), true, false, true, false, false);
		mCfgComponents.remove("root");
		// error, error state
		icfg.addLocation(mCfgComponents.get("error").getStart(), false, true, false, true, false);
		mCfgComponents.remove("error");
		// push the remaining locations into the icfg
		mCfgComponents.forEach((id, comp) -> {
			// start is proc_entry + end is proc_exit
			icfg.addOrdinaryLocation(comp.getStart());
			icfg.addOrdinaryLocation(comp.getEnd());
			for (final BoogieIcfgLocation loc : comp.getLocations()) {
				icfg.addOrdinaryLocation(loc);
			}
		});
		mLogger.debug("################# ICFG ###################");
		mLogger.debug(icfg.getProgramPoints().toString());
		mLogger.debug(icfg.getSymboltable().getLocals("MAIN").toString());
		return icfg;
	}
	
	public void modelToIcfg(final HybridAutomaton aut) {
		/*
		 * in order to convert the hybrid model to an ICFG, we have to convert the parallelComposition of the regarded
		 * system.
		 */
		if (aut == null) {
			throw new IllegalStateException("HybridAutomaton aut has not been assigned and is null");
		} else {
			// convert automaton to cfg components
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
		transitionsToIcfg(transitions, initialLocation);
	}
	
	/*
	 * variable methods
	 */
	private void variablesToIcfg(final Set<String> variables) {
		final Script script = mSmtToolkit.getManagedScript().getScript();
		// get initial values of the variable
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, true, null, true, null, true);
		for (final String var : variables) {
			// Termvariables for the transformula.
			final TermVariable inVar =
					mSmtToolkit.getManagedScript().constructFreshTermVariable(var, script.sort("Real"));
			final TermVariable outVar =
					mSmtToolkit.getManagedScript().constructFreshTermVariable(var, script.sort("Real"));
			mVariableManager.addInVarTermVariable(var, inVar);
			mVariableManager.addOutVarTermVariable(var, outVar);
			// IProgramVar for the transformula.
			final HybridProgramVar progVar = mVariableManager.constructProgramVar(var, mProcedure);
			mVariableManager.addProgramVar(var, progVar);
			tfb.addInVar(progVar, inVar);
			tfb.addOutVar(progVar, outVar);
		}
		UnmodifiableTransFormula transformula;
		final String infix = mSpaceExPreferenceManager.getInitialInfix();
		if (infix.isEmpty()) {
			transformula = TransFormulaBuilder.getTrivialTransFormula(mSmtToolkit.getManagedScript());
		} else {
			final HybridTermBuilder tb = new HybridTermBuilder(mVariableManager, script);
			final Term term = tb.infixToTerm(infix, BuildScenario.INITIALLY);
			mLogger.info(term);
			tfb.setFormula(term);
			tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
			// finish construction of the transformula.
			transformula = tfb.finishConstruction(mSmtToolkit.getManagedScript());
		}
		mLogger.debug("Transformula for varAssignment: " + transformula);
		// create variable component of the form start ----variable assignment----> end
		final List<BoogieIcfgLocation> locations = new ArrayList<>();
		final List<IcfgInternalTransition> transitions = new ArrayList<>();
		final String id = "varAssignment";
		final BoogieIcfgLocation start = new BoogieIcfgLocation(id + "_start", mProcedure, false, mBoogieASTNode);
		final BoogieIcfgLocation end = new BoogieIcfgLocation(id + "_end", mProcedure, false, mBoogieASTNode);
		final IcfgInternalTransition startEnd = new IcfgInternalTransition(start, end, mPayload, transformula);
		start.addOutgoing(startEnd);
		end.addIncoming(startEnd);
		transitions.add(startEnd);
		// new cfgComponent, has to be connected to the root node.
		mCfgComponents.put(id, new HybridCfgComponent(id, start, end, locations, transitions));
		/*
		 * Transition from Root to varAssignment
		 */
		// the source of the transition is the the end of the source CFG component
		final BoogieIcfgLocation source = mCfgComponents.get("root").getEnd();
		// the target of the transition is the the start of the target CFG component
		final BoogieIcfgLocation target = mCfgComponents.get("varAssignment").getStart();
		final UnmodifiableTransFormula transFormula =
				TransFormulaBuilder.getTrivialTransFormula(mSmtToolkit.getManagedScript());
		final IcfgInternalTransition transition = new IcfgInternalTransition(source, target, mPayload, transFormula);
		source.addOutgoing(transition);
		target.addIncoming(transition);
	}
	
	/*
	 * Location methods
	 */
	private void locationsToIcfg(final Map<Integer, Location> autLocations) {
		/*
		 * locations consist of Flow and the invariant. -> Startnode (1) -> if/else invariant (2) -> apply flow (3) ->
		 * if/else invariant (4)
		 */
		for (final Map.Entry<Integer, Location> entry : autLocations.entrySet()) {
			final Integer autid = entry.getKey();
			final Location loc = entry.getValue();
			final List<IcfgInternalTransition> transitions = new ArrayList<>();
			final List<BoogieIcfgLocation> locations = new ArrayList<>();
			/*
			 * Locations: Start, End, Flow, InvariantCheck
			 */
			final BoogieIcfgLocation start =
					new BoogieIcfgLocation(autid + "_start", mProcedure, false, mBoogieASTNode);
			final BoogieIcfgLocation end = new BoogieIcfgLocation(autid + "_end", mProcedure, false, mBoogieASTNode);
			final BoogieIcfgLocation flow = new BoogieIcfgLocation(autid + "_flow", mProcedure, false, mBoogieASTNode);
			locations.add(flow);
			final BoogieIcfgLocation invCheck =
					new BoogieIcfgLocation(autid + "_invCheck", mProcedure, false, mBoogieASTNode);
			locations.add(invCheck);
			/*
			 * Transitions from start to Flow if invariant true
			 */
			// invariant to term:
			final String infix = preprocessLocationStatement(loc.getInvariant());
			final UnmodifiableTransFormula invariantTransformula = buildTransformula(infix, BuildScenario.INVARIANT);
			final String msg = createTransformulaLoggerMessage(invariantTransformula, infix);
			mLogger.info(msg);
			final UnmodifiableTransFormula tfStartFlow = invariantTransformula;
			final IcfgInternalTransition startFlow = new IcfgInternalTransition(start, flow, mPayload, tfStartFlow);
			start.addOutgoing(startFlow);
			flow.addIncoming(startFlow);
			transitions.add(startFlow);
			
			/*
			 * Transition flow to invCheck
			 */
			final UnmodifiableTransFormula tfFlowInv =
					TransFormulaBuilder.getTrivialTransFormula(mSmtToolkit.getManagedScript());
			final IcfgInternalTransition flowInv = new IcfgInternalTransition(flow, invCheck, mPayload, tfFlowInv);
			flow.addOutgoing(flowInv);
			invCheck.addIncoming(flowInv);
			transitions.add(flowInv);
			/*
			 * Transition invCheck to end/exit if invariant true, go to end, else to error loc
			 */
			// invcheck -> end
			final UnmodifiableTransFormula tfInvEnd = invariantTransformula;
			final IcfgInternalTransition invEnd = new IcfgInternalTransition(invCheck, end, mPayload, tfInvEnd);
			invCheck.addOutgoing(invEnd);
			end.addIncoming(invEnd);
			transitions.add(invEnd);
			// create new cfgComponent
			mCfgComponents.put(autid.toString(),
					new HybridCfgComponent(autid.toString(), start, end, locations, transitions));
		}
	}
	
	/*
	 * Transition methods
	 */
	private void transitionsToIcfg(final List<Transition> transitions, Location initialLocation) {
		// a transition in a hybrid automaton is simply an edge from one location to another.
		// guard and update can be merged with &&
		transitions.forEach(trans -> {
			// the source of the transition is the the end of the source CFG component
			final BoogieIcfgLocation source = mCfgComponents.get(Integer.toString(trans.getSourceId())).getEnd();
			// the target of the transition is the the start of the target CFG component
			final BoogieIcfgLocation target = mCfgComponents.get(Integer.toString(trans.getTargetId())).getStart();
			// invariant to term:
			final UnmodifiableTransFormula transFormula =
					buildTransitionTransformula(trans.getUpdate(), trans.getGuard());
			final String msg =
					createTransformulaLoggerMessage(transFormula, trans.getUpdate() + " && " + trans.getGuard());
			mLogger.info(msg);
			final IcfgInternalTransition transition =
					new IcfgInternalTransition(source, target, mPayload, transFormula);
			source.addOutgoing(transition);
			target.addIncoming(transition);
		});
		
		// the source of the transition is the the end of the source CFG component
		final BoogieIcfgLocation source = mCfgComponents.get("varAssignment").getEnd();
		// the target of the transition is the the start of the target CFG component
		final BoogieIcfgLocation target = mCfgComponents.get(Integer.toString(initialLocation.getId())).getStart();
		final UnmodifiableTransFormula transFormula =
				TransFormulaBuilder.getTrivialTransFormula(mSmtToolkit.getManagedScript());
		final IcfgInternalTransition transition = new IcfgInternalTransition(source, target, mPayload, transFormula);
		source.addOutgoing(transition);
		target.addIncoming(transition);
		
	}
	
	private String createTransformulaLoggerMessage(UnmodifiableTransFormula transFormula, String infix) {
		String msg = "######## CREATED TRANSFORMULA ######## \n";
		msg += "created " + transFormula.toString() + "\n";
		msg += "infix: " + infix;
		return msg;
	}
	
	private UnmodifiableTransFormula buildTransitionTransformula(String update, String guard) {
		final HybridTermBuilder tb =
				new HybridTermBuilder(mVariableManager, mSmtToolkit.getManagedScript().getScript());
		UnmodifiableTransFormula transformula;
		Term formula = null;
		if (update.isEmpty() && guard.isEmpty()) {
			formula = mSmtToolkit.getManagedScript().getScript().term("true");
		} else if (!update.isEmpty() && !guard.isEmpty()) {
			final Term guardTerm = tb.infixToTerm(preprocessLocationStatement(guard), BuildScenario.GUARD);
			final Term updateTerm = tb.infixToTerm(preprocessLocationStatement(update), BuildScenario.UPDATE);
			formula = mSmtToolkit.getManagedScript().getScript().term("and", updateTerm, guardTerm);
		} else if (update.isEmpty() && !guard.isEmpty()) {
			formula = tb.infixToTerm(preprocessLocationStatement(guard), BuildScenario.GUARD);
		} else if (!update.isEmpty() && guard.isEmpty()) {
			formula = tb.infixToTerm(preprocessLocationStatement(update), BuildScenario.UPDATE);
		}
		// TFB
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, true, null, true, null, true);
		tb.getmInVars().forEach((progvar, invar) -> {
			tfb.addInVar(progvar, invar);
		});
		tb.getmOutVars().forEach((progvar, outvar) -> {
			tfb.addOutVar(progvar, outvar);
		});
		tfb.setFormula(formula);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		// finish construction of the transformula.
		transformula = tfb.finishConstruction(mSmtToolkit.getManagedScript());
		mLogger.debug("Transformula for varAssignment: " + transformula);
		return transformula;
	}
	
	private UnmodifiableTransFormula buildTransformula(String infix, BuildScenario scenario) {
		final HybridTermBuilder tb =
				new HybridTermBuilder(mVariableManager, mSmtToolkit.getManagedScript().getScript());
		final Term term = tb.infixToTerm(infix, scenario);
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, true, null, true, null, true);
		tb.getmInVars().forEach((progvar, invar) -> {
			tfb.addInVar(progvar, invar);
		});
		tb.getmOutVars().forEach((progvar, outvar) -> {
			tfb.addOutVar(progvar, outvar);
		});
		tfb.setFormula(term);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		// finish construction of the transformula.
		final UnmodifiableTransFormula transformula = tfb.finishConstruction(mSmtToolkit.getManagedScript());
		mLogger.debug("Transformula for varAssignment: " + transformula);
		return transformula;
	}
	
	private String preprocessLocationStatement(String invariant) {
		String inv = invariant.replaceAll(":=", "==");
		inv = inv.replaceAll("&&", "&");
		return inv;
	}
}
