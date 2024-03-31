package de.uni_freiburg.informatik.ultimate.btortranslator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.btorutils.AssignmentRule;
import de.uni_freiburg.informatik.ultimate.btorutils.BtorExpression;
import de.uni_freiburg.informatik.ultimate.btorutils.BtorExpressionType;
import de.uni_freiburg.informatik.ultimate.btorutils.UpdateRule;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class CFGToBTORTranslator {
	private final HashMap<String, BtorExpression> variableMap;
	private final HashMap<DebugIdentifier, List<UpdateRule>> locationUpdateMap;
	private final HashMap<String, List<AssignmentRule>> variableAssignmentMap;
	private Map<String, Map<DebugIdentifier, IcfgLocation>> allLocations;
	ManagedScript mScript;
	IUltimateServiceProvider mService;

	public CFGToBTORTranslator(final ManagedScript script, final IUltimateServiceProvider service) {
		mScript = script;
		mService = service;
		variableMap = new HashMap<>();
		locationUpdateMap = new HashMap<>();
		variableAssignmentMap = new HashMap<>();
	}

	public void extractVariables(final IIcfg<IcfgLocation> icfg) {
		final Set<IProgramVar> allVariables = IcfgUtils.collectAllProgramVars(icfg.getCfgSmtToolkit());
		for (final IProgramVar var : allVariables) {
			int sort;
			if (var.getSort().getName() == "Int") {
				sort = 64;
			} else if (var.getSort().getName() == "Bool") {
				sort = 1;
			} else {
				throw new UnsupportedOperationException("sort is not int or bool");
			}

			final BtorExpression newState = new BtorExpression(sort, BtorExpressionType.STATE, new ArrayList<>());
			variableMap.put(var.getGloballyUniqueId(), newState);
		}
	}

	public void extractLocations(final IIcfg<IcfgLocation> icfg) {
		allLocations = icfg.getProgramPoints();
	}

	public void extractTransitions(final IIcfg<IcfgLocation> icfg) {
		for (final Map<DebugIdentifier, IcfgLocation> procedure : allLocations.values()) {
			for (final IcfgLocation location : procedure.values()) {
				final List<UpdateRule> updateRules = new ArrayList<>();
				final List<IcfgEdge> outgoing = location.getOutgoingEdges();
				for (final IcfgEdge edge : outgoing) {
					final UnmodifiableTransFormula transitionFormula = edge.getTransformula();
					final Term guard =
							TransFormulaUtils.computeGuard(transitionFormula, mScript, mService).getFormula();
					updateRules.add(new UpdateRule(guard, edge.getTarget().getDebugIdentifier()));
				}
				locationUpdateMap.put(location.getDebugIdentifier(), updateRules);
			}
		}
	}

	public void extractAssignments(final IIcfg<IcfgLocation> icfg) {
		for (final Map<DebugIdentifier, IcfgLocation> procedure : allLocations.values()) {
			for (final IcfgLocation location : procedure.values()) {
				final List<IcfgEdge> outgoing = location.getOutgoingEdges();
				for (final IcfgEdge edge : outgoing) { // TODO: for loop unnecessary if assignments have no guards
					final UnmodifiableTransFormula transitionFormula = edge.getTransformula();
					final List<AssignmentRule> assignments = AssignmentRule
							.getAssignmentsFromTransition(location.getDebugIdentifier(), transitionFormula);
					for (final AssignmentRule assignment : assignments) {
						if (variableAssignmentMap.containsKey(assignment.lhs.getGloballyUniqueId())) {
							variableAssignmentMap.get(assignment.lhs.getGloballyUniqueId()).add(assignment);
						} else {
							final List<AssignmentRule> a = new ArrayList<>();
							a.add(assignment);
							variableAssignmentMap.put(assignment.lhs.getGloballyUniqueId(), a);
						}
					}
				}
			}
		}
	}
}

// gather cfg locations
// gather cfg transitions
// gather all constants

// comment

// initialize pc, 0, 1, constants
