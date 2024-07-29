package de.uni_freiburg.informatik.ultimate.btortranslator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.btorutils.AssignmentRule;
import de.uni_freiburg.informatik.ultimate.btorutils.BtorExpression;
import de.uni_freiburg.informatik.ultimate.btorutils.BtorExpressionType;
import de.uni_freiburg.informatik.ultimate.btorutils.BtorScript;
import de.uni_freiburg.informatik.ultimate.btorutils.UpdateRule;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class CFGToBTOR {
	private final HashMap<String, BtorExpression> variableMap;
	private final HashMap<DebugIdentifier, List<UpdateRule>> locationUpdateMap;
	private final HashMap<String, List<AssignmentRule>> variableAssignmentMap;
	private Map<String, Map<DebugIdentifier, IcfgLocation>> allLocations;
	private final Set<DebugIdentifier> errorLocations;
	private final Map<DebugIdentifier, BtorExpression> pcMap;
	private final BtorExpression pcExpression;
	ManagedScript mScript;
	IUltimateServiceProvider mService;

	public CFGToBTOR(final ManagedScript script, final IUltimateServiceProvider service) {
		mScript = script;
		mService = service;
		variableMap = new HashMap<>();
		locationUpdateMap = new HashMap<>();
		errorLocations = new HashSet<>();
		variableAssignmentMap = new HashMap<>();
		pcMap = new HashMap<>();
		pcExpression = new BtorExpression(64, BtorExpressionType.STATE, new ArrayList<>());
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
					updateRules.add(new UpdateRule(guard, edge.getTarget().getDebugIdentifier(), transitionFormula));
				}
				locationUpdateMap.put(location.getDebugIdentifier(), updateRules);
			}
		}
	}

	/**
	 * public void extractAssignments(final IIcfg<IcfgLocation> icfg) { for (final Map<DebugIdentifier, IcfgLocation>
	 * procedure : allLocations.values()) { for (final IcfgLocation location : procedure.values()) { final
	 * List<IcfgEdge> outgoing = location.getOutgoingEdges(); for (final IcfgEdge edge : outgoing) { // TODO: for loop
	 * unnecessary if assignments have no guards final UnmodifiableTransFormula transitionFormula =
	 * edge.getTransformula(); final List<AssignmentRule> assignments = AssignmentRule
	 * .getAssignmentsFromTransition(location.getDebugIdentifier(), transitionFormula, mScript); for (final
	 * AssignmentRule assignment : assignments) { if
	 * (variableAssignmentMap.containsKey(assignment.lhs.getGloballyUniqueId())) {
	 * variableAssignmentMap.get(assignment.lhs.getGloballyUniqueId()).add(assignment); } else { final
	 * List<AssignmentRule> a = new ArrayList<>(); a.add(assignment);
	 * variableAssignmentMap.put(assignment.lhs.getGloballyUniqueId(), a); } } } } } }
	 */

	public void extractBadStates(final IIcfg<IcfgLocation> icfg) {

		for (final IcfgLocation errorLocation : IcfgUtils.getErrorLocations(icfg)) {
			errorLocations.add(errorLocation.getDebugIdentifier());
		}
	}

	private void generateAssignments(final DebugIdentifier location, final TransFormula tf,
			final BtorExpression guard) {
		final List<AssignmentRule> assignments =
				AssignmentRule.getAssignmentsFromTransition(location, tf, mScript, guard);
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

	private BtorExpression generatePCUpdateExpression() {
		int pc = 1;
		for (final DebugIdentifier locID : locationUpdateMap.keySet()) {
			pcMap.put(locID, new BtorExpression(64, pc));
			System.out.println("locID: " + locID + " pc: " + pc);
			pc++;
		}
		final BtorExpression zero = new BtorExpression(64, BtorExpressionType.ZERO, new ArrayList<>());
		BtorExpression latestITE = zero;
		for (final DebugIdentifier locID : locationUpdateMap.keySet()) {
			BtorExpression latestUpdate = zero;
			final List<UpdateRule> updates = locationUpdateMap.get(locID);

			final BtorExpression lineCheck =
					new BtorExpression(1, BtorExpressionType.EQ, Arrays.asList(pcExpression, pcMap.get(locID)));
			if (updates.size() == 1) {
				final BtorExpression guard = updates.get(0).getConditionAsExpression(variableMap);
				latestUpdate = new BtorExpression(64, BtorExpressionType.ITE,
						Arrays.asList(guard, pcMap.get(updates.get(0).getTargetIdentifier()), latestUpdate));
				generateAssignments(locID, updates.get(0).getTransFormula(), guard);

			} else { // generateAssignments(DebugIdentifier location, TransFormula tf, BtorExpression guard)
				// sort update rules
				int i = 0;
				int swapIndex = updates.size() - 1;
				while (i < swapIndex) {
					if (SmtUtils.isTrueLiteral(updates.get(i).getCondition())) {
						Collections.swap(updates, i, swapIndex);
						i++;
					}
					swapIndex--;
				}

				for (final UpdateRule update : updates) {
					if (SmtUtils.isTrueLiteral(update.getCondition())) {
						final BtorExpression nondeterministicGuard =
								new BtorExpression(1, BtorExpressionType.INPUT, new ArrayList<>());
						latestUpdate = new BtorExpression(64, BtorExpressionType.ITE, Arrays
								.asList(nondeterministicGuard, pcMap.get(update.getTargetIdentifier()), latestUpdate));
						generateAssignments(locID, update.getTransFormula(), nondeterministicGuard);
					} else {
						final BtorExpression guard = update.getConditionAsExpression(variableMap);
						latestUpdate = new BtorExpression(64, BtorExpressionType.ITE,
								Arrays.asList(guard, pcMap.get(update.getTargetIdentifier()), latestUpdate));
						generateAssignments(locID, update.getTransFormula(), guard);
					}
				}
			}

			/**
			 * if (updates.size() == 2 && SmtUtils.isTrueLiteral(updates.get(0).getCondition()) &&
			 * SmtUtils.isTrueLiteral(updates.get(1).getCondition())) { final BtorExpression nondeterministicGuard = new
			 * BtorExpression(1, BtorExpressionType.INPUT, new ArrayList<>()); latestUpdate = new BtorExpression(64,
			 * BtorExpressionType.ITE, Arrays.asList(nondeterministicGuard,
			 * pcMap.get(updates.get(0).getTargetIdentifier()), pcMap.get(updates.get(1).getTargetIdentifier()))); }
			 */
			latestITE =
					new BtorExpression(64, BtorExpressionType.ITE, Arrays.asList(lineCheck, latestUpdate, latestITE));
		}
		final BtorExpression next =
				new BtorExpression(64, BtorExpressionType.NEXT, Arrays.asList(pcExpression, latestITE));
		return next;
	}

	private List<BtorExpression> generateVariableUpdateExpressions() {
		final ArrayList<BtorExpression> updateExpressions = new ArrayList<>();
		for (final String var : variableAssignmentMap.keySet()) {
			final BtorExpression varExpression = variableMap.get(var);
			BtorExpression lastITE = varExpression;
			for (final AssignmentRule rule : variableAssignmentMap.get(var)) {
				final BtorExpression rhsExpression = rule.getRHSAsExpression(variableMap);
				final BtorExpression lineCheck = new BtorExpression(1, BtorExpressionType.EQ,
						Arrays.asList(pcExpression, pcMap.get(rule.assignmentLocationIdentifier)));
				final BtorExpression lineAndGuardCheck =
						new BtorExpression(1, BtorExpressionType.AND, Arrays.asList(lineCheck, rule.guard));
				lastITE = new BtorExpression(varExpression.getSort(), BtorExpressionType.ITE,
						Arrays.asList(lineAndGuardCheck, rhsExpression, lastITE));
			}
			final BtorExpression next = new BtorExpression(varExpression.getSort(), BtorExpressionType.NEXT,
					Arrays.asList(varExpression, lastITE));
			updateExpressions.add(next);
		}
		return updateExpressions;
	}

	// generates a list of corresponding bad expressions given the list of error locations
	private List<BtorExpression> generateBadExpressions() {
		final ArrayList<BtorExpression> badExpressions = new ArrayList<>();
		for (final DebugIdentifier errorLocation : errorLocations) {
			final BtorExpression eq =
					new BtorExpression(1, BtorExpressionType.EQ, Arrays.asList(pcExpression, pcMap.get(errorLocation)));
			final BtorExpression badExpression = new BtorExpression(1, BtorExpressionType.BAD, Arrays.asList(eq));
			badExpressions.add(badExpression);
		}
		return badExpressions;
	}

	public BtorScript generateScript(final IIcfg<IcfgLocation> icfg) {
		final BtorExpression pcUpdate = generatePCUpdateExpression();
		final Set<IcfgLocation> initial = icfg.getInitialNodes();
		if (initial.size() != 1) {
			throw new UnsupportedOperationException("Multiple initial states");
		}
		final BtorExpression initial_pc = pcMap.get(initial.iterator().next().getDebugIdentifier());
		final BtorExpression pc_initialization =
				new BtorExpression(64, BtorExpressionType.INIT, Arrays.asList(pcExpression, initial_pc));
		final List<BtorExpression> variableUpdateExpressions = generateVariableUpdateExpressions();
		final List<BtorExpression> allTopLevelExpressions =
				new ArrayList<>(Arrays.asList(initial_pc, pc_initialization, pcUpdate));
		final List<BtorExpression> badExpressions = generateBadExpressions();
		allTopLevelExpressions.addAll(variableUpdateExpressions);
		allTopLevelExpressions.addAll(badExpressions);
		return new BtorScript(allTopLevelExpressions, Arrays.asList(1, 64));
	}

}
