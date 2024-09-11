package de.uni_freiburg.informatik.ultimate.btortranslator;

import java.beans.Expression;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
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
import de.uni_freiburg.informatik.ultimate.btorutils.BtorSort;
import de.uni_freiburg.informatik.ultimate.btorutils.UpdateRule;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.SuffixedDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;

public class CFGToBTOR {
	private final HashMap<String, BtorExpression> variableMap;
	private final HashMap<SuffixedDebugIdentifier, List<UpdateRule>> locationUpdateMap;
	private final HashMap<String, List<AssignmentRule>> variableAssignmentMap;
	private Map<String, Map<DebugIdentifier, BoogieIcfgLocation>> allLocations;
	private final Set<DebugIdentifier> errorLocations;
	private final Map<SuffixedDebugIdentifier, BtorExpression> pcMap;
	private final BtorExpression pcExpression;
	// private final Boogie2SmtSymbolTable B2STable;
	ManagedScript mScript;
	IUltimateServiceProvider mService;/////
	private final Boogie2SMT boogie2SMT;

	public CFGToBTOR(final ManagedScript script, final IUltimateServiceProvider service, final Boogie2SMT boogie2SMT) {
		mScript = script;
		mService = service;
		variableMap = new HashMap<>();
		locationUpdateMap = new HashMap<>();
		errorLocations = new HashSet<>();
		variableAssignmentMap = new HashMap<>();
		pcMap = new HashMap<>();
		pcExpression = new BtorExpression(new BtorSort(64), "pc");
		this.boogie2SMT = boogie2SMT;
	}

	public void extractVariables(final IIcfg<BoogieIcfgLocation> icfg) {
		final Set<IProgramVar> allVariables = IcfgUtils.collectAllProgramVars(icfg.getCfgSmtToolkit());
		for (final IProgramVar var : allVariables) {
			final BtorSort sort = new BtorSort(var.getSort());
			final BtorExpression newState = new BtorExpression(sort, var.getGloballyUniqueId());
			variableMap.put(var.getGloballyUniqueId(), newState);
		}
	}

	public void extractLocations(final IIcfg<BoogieIcfgLocation> icfg) {
		allLocations = icfg.getProgramPoints();
	}

	public void extractTransitions(final IIcfg<BoogieIcfgLocation> icfg) {
		for (final String procedure : allLocations.keySet()) {
			final Map<DebugIdentifier, BoogieIcfgLocation> procedureLocations = allLocations.get(procedure);
			for (final DebugIdentifier debugIdentifier : procedureLocations.keySet()) {
				final BoogieIcfgLocation location = procedureLocations.get(debugIdentifier);
				final List<UpdateRule> updateRules = new ArrayList<>();
				final List<IcfgEdge> outgoing = location.getOutgoingEdges();
				for (final IcfgEdge edge : outgoing) {

					final UnmodifiableTransFormula transitionFormula = edge.getTransformula();
					final Term guard =
							TransFormulaUtils.computeGuard(transitionFormula, mScript, mService).getFormula();
					updateRules.add(
							new UpdateRule(guard, new SuffixedDebugIdentifier(edge.getTarget().getDebugIdentifier(),
									edge.getTarget().getProcedure()), transitionFormula, edge));
				}
				locationUpdateMap.put(new SuffixedDebugIdentifier(debugIdentifier, procedure), updateRules);
			}
		}
	}

	// public void extractTransitions(final IIcfg<BoogieIcfgLocation> icfg) {
	// for (final Map<DebugIdentifier, BoogieIcfgLocation> procedure : allLocations.values()) {
	// for (final BoogieIcfgLocation location : procedure.values()) {
	// final List<UpdateRule> updateRules = new ArrayList<>();
	// final List<IcfgEdge> outgoing = location.getOutgoingEdges();
	// for (final IcfgEdge edge : outgoing) {
	// // if (edge instanceof Return) {
	// // final Return retEdge = (Return) edge;
	// // final int k = 1 + 1;
	// // icfg.getCfgSmtToolkit().getOutParams()
	// // .get(retEdge.getCorrespondingCall().getSucceedingProcedure());
	// // // retEdge.getCallStatement().getLhs()[0].getIdentifier();
	// // // final BoogieIcfgContainer bicfg = (BoogieIcfgContainer) icfg;
	// // // bicfg.getBoogie2SMT().getBoogie2SmtSymbolTable()
	// //
	// // }
	// final UnmodifiableTransFormula transitionFormula = edge.getTransformula();
	// final Term guard =
	// TransFormulaUtils.computeGuard(transitionFormula, mScript, mService).getFormula();
	// updateRules.add(new UpdateRule(guard, edge.getTarget().getDebugIdentifier(), transitionFormula));
	// }
	// locationUpdateMap.put(location.getDebugIdentifier(), updateRules);
	// }
	// }
	// }

	/**
	 * public void extractAssignments(final IIcfg<BoogieIcfgLocation> icfg) { for (final Map<DebugIdentifier,
	 * BoogieIcfgLocation> procedure : allLocations.values()) { for (final BoogieIcfgLocation location :
	 * procedure.values()) { final List<IcfgEdge> outgoing = location.getOutgoingEdges(); for (final IcfgEdge edge :
	 * outgoing) { // TODO: for loop unnecessary if assignments have no guards final UnmodifiableTransFormula
	 * transitionFormula = edge.getTransformula(); final List<AssignmentRule> assignments = AssignmentRule
	 * .getAssignmentsFromTransition(location.getDebugIdentifier(), transitionFormula, mScript); for (final
	 * AssignmentRule assignment : assignments) { if
	 * (variableAssignmentMap.containsKey(assignment.lhs.getGloballyUniqueId())) {
	 * variableAssignmentMap.get(assignment.lhs.getGloballyUniqueId()).add(assignment); } else { final
	 * List<AssignmentRule> a = new ArrayList<>(); a.add(assignment);
	 * variableAssignmentMap.put(assignment.lhs.getGloballyUniqueId(), a); } } } } } }
	 */

	public void extractBadStates(final IIcfg<BoogieIcfgLocation> icfg) {

		for (final BoogieIcfgLocation errorLocation : IcfgUtils.getErrorLocations(icfg)) {
			errorLocations
					.add(new SuffixedDebugIdentifier(errorLocation.getDebugIdentifier(), errorLocation.getProcedure()));
		}
	}

	private void generateAssignments(final DebugIdentifier location, final TransFormula tf, final IcfgEdge icfgEdge,
			final BtorExpression guard) {

		try {
			final Set<TermVariable> auxVars = new HashSet<>(tf.getAuxVars());
			final IProgramVar av = tf.getAssignedVars().iterator().next();
			final TermVariable outVar = tf.getOutVars().get(av);
			for (final TermVariable bv : tf.getInVars().values()) {
				if (!bv.equals(outVar)) {
					auxVars.add(bv);
				}
			}
			for (final TermVariable bv : tf.getOutVars().values()) {
				if (!bv.equals(outVar)) {
					auxVars.add(bv);
				}
			}

			final Term quantifiedTerm =
					SmtUtils.quantifier(mScript.getScript(), QuantifiedFormula.EXISTS, auxVars, tf.getFormula());
			final Term resultTerm = PartialQuantifierElimination.eliminate(mService, mScript, quantifiedTerm,
					SimplificationTechnique.POLY_PAC);
			final int i = 1 + 1;

		} catch (final Exception e) {

		}

		final Expression e = null;
		final List<AssignmentRule> assignments =
				AssignmentRule.getAssignmentsFromTransition(location, icfgEdge, mScript, guard, boogie2SMT);
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
		for (final SuffixedDebugIdentifier locID : locationUpdateMap.keySet()) {
			pcMap.put(locID, new BtorExpression(new BtorSort(64), pc));
			System.out.println("locID: " + locID + " pc: " + pc);
			pc++;
		}
		final BtorExpression zero = new BtorExpression(new BtorSort(64), BtorExpressionType.ZERO, new ArrayList<>());
		BtorExpression latestITE = zero;
		for (final SuffixedDebugIdentifier locID : locationUpdateMap.keySet()) {
			BtorExpression latestUpdate = zero;
			final List<UpdateRule> updates = locationUpdateMap.get(locID);

			final BtorExpression lineCheck = new BtorExpression(new BtorSort(1), BtorExpressionType.EQ,
					Arrays.asList(pcExpression, pcMap.get(locID)));
			if (updates.size() == 1) {
				final BtorExpression guard = updates.get(0).getConditionAsExpression(variableMap);
				latestUpdate = new BtorExpression(new BtorSort(64), BtorExpressionType.ITE,
						Arrays.asList(guard, pcMap.get(updates.get(0).getTargetIdentifier()), latestUpdate));
				generateAssignments(locID, updates.get(0).getTransFormula(), updates.get(0).getIcfgEdge(), guard);

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
								new BtorExpression(new BtorSort(1), BtorExpressionType.INPUT, new ArrayList<>());
						latestUpdate = new BtorExpression(new BtorSort(64), BtorExpressionType.ITE, Arrays
								.asList(nondeterministicGuard, pcMap.get(update.getTargetIdentifier()), latestUpdate));
						generateAssignments(locID, update.getTransFormula(), update.getIcfgEdge(),
								nondeterministicGuard);
					} else {
						final BtorExpression guard = update.getConditionAsExpression(variableMap);
						latestUpdate = new BtorExpression(new BtorSort(64), BtorExpressionType.ITE,
								Arrays.asList(guard, pcMap.get(update.getTargetIdentifier()), latestUpdate));
						generateAssignments(locID, update.getTransFormula(), update.getIcfgEdge(), guard);
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
			latestITE = new BtorExpression(new BtorSort(64), BtorExpressionType.ITE,
					Arrays.asList(lineCheck, latestUpdate, latestITE));
		}
		final BtorExpression next =
				new BtorExpression(new BtorSort(64), BtorExpressionType.NEXT, Arrays.asList(pcExpression, latestITE));
		return next;
	}

	private List<BtorExpression> generateVariableUpdateExpressions() {
		final ArrayList<BtorExpression> updateExpressions = new ArrayList<>();
		for (final String var : variableMap.keySet()) {
			final BtorExpression varExpression = variableMap.get(var);
			BtorExpression lastITE = varExpression;

			if (variableAssignmentMap.get(var) == null) {
				final BtorExpression next = new BtorExpression(varExpression.getSort(), BtorExpressionType.NEXT,
						Arrays.asList(varExpression, varExpression));
				updateExpressions.add(next);
				continue;
			}
			for (final AssignmentRule rule : variableAssignmentMap.get(var)) {
				final BtorExpression rhsExpression = rule.getRHSAsExpression(variableMap);
				final BtorExpression lineCheck = new BtorExpression(new BtorSort(1), BtorExpressionType.EQ,
						Arrays.asList(pcExpression, pcMap.get(rule.assignmentLocationIdentifier)));
				final BtorExpression lineAndGuardCheck = new BtorExpression(new BtorSort(1), BtorExpressionType.AND,
						Arrays.asList(lineCheck, rule.guard));
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
			final BtorExpression eq = new BtorExpression(new BtorSort(1), BtorExpressionType.EQ,
					Arrays.asList(pcExpression, pcMap.get(errorLocation)));
			final BtorExpression badExpression =
					new BtorExpression(new BtorSort(1), BtorExpressionType.BAD, Arrays.asList(eq));
			badExpressions.add(badExpression);
		}
		return badExpressions;
	}

	public IcfgProgramExecution<IcfgEdge> extractErrorTrace(final IIcfg<BoogieIcfgLocation> icfg,
			final ArrayList<Long> pcList, final Map<Long, Map<String, Long>> programStateSequence) {
		final List<IcfgEdge> edges = new ArrayList<>();
		final List<BoogieIcfgLocation> locs = new ArrayList<>();
		final Map<Long, SuffixedDebugIdentifier> pcToDI = new HashMap<>();
		for (final SuffixedDebugIdentifier ident : pcMap.keySet()) {
			pcToDI.put(pcMap.get(ident).getConstant(), ident);
		}
		// final Map<DebugIdentifier, BoogieIcfgLocation> diToLoc = icfg.getProgramPoints().values().iterator().next();
		final Map<DebugIdentifier, BoogieIcfgLocation> diToLoc = new HashMap<>();
		final Collection<Map<DebugIdentifier, BoogieIcfgLocation>> temp = icfg.getProgramPoints().values();

		for (final Map<DebugIdentifier, BoogieIcfgLocation> prodecureLocations : temp) {
			final Set<DebugIdentifier> keys = prodecureLocations.keySet();
			for (final DebugIdentifier key : keys) {
				final BoogieIcfgLocation loc = prodecureLocations.get(key);
				final SuffixedDebugIdentifier suffixedKey = new SuffixedDebugIdentifier(key, loc.getProcedure());
				diToLoc.put(suffixedKey, prodecureLocations.get(key));
			}
		}
		for (final Long pc : pcList) {
			locs.add(diToLoc.get(pcToDI.get((long) pc)));
		}
		for (int i = 0; i < locs.size() - 1; i++) {
			final BoogieIcfgLocation loc = locs.get(i);
			final BoogieIcfgLocation nextLoc = locs.get(i + 1);
			final List<IcfgEdge> outgoingEdges = loc.getOutgoingEdges();
			for (final IcfgEdge outgoingEdge : outgoingEdges) {
				if (outgoingEdge.getTarget().equals(nextLoc)) {
					edges.add(outgoingEdge);
					break;
				}
			}
		}
		final Set<IProgramVar> allVariables = IcfgUtils.collectAllProgramVars(icfg.getCfgSmtToolkit());
		final Map<Integer, ProgramState<Term>> partialProgramStateMapping = new HashMap<>();
		for (final long sequenceNumber : programStateSequence.keySet()) {
			if (sequenceNumber == 0) {
				continue;
			}
			final Map<Term, Collection<Term>> programStates = new HashMap<>();
			final Map<String, Long> assignmentMapping = programStateSequence.get(sequenceNumber);
			for (final String varName : assignmentMapping.keySet()) {
				for (final IProgramVar variable : allVariables) {
					if (varName.equals(variable.getGloballyUniqueId())) {
						Term value = null;
						switch (variable.getSort().getName()) {
						case "Int":
							value = SmtUtils.constructIntValue(mScript.getScript(),
									BigInteger.valueOf(assignmentMapping.get(varName)));
							break;
						case "Bool":
							if (Long.valueOf(assignmentMapping.get(varName)) == 1) {
								value = mScript.getScript().term("true");
							} else {
								value = mScript.getScript().term("false");
							}
							break;
						case "BitVec":
							value = SmtUtils.constructIntegerValue(mScript.getScript(), variable.getSort(),
									BigInteger.valueOf(assignmentMapping.get(varName)));
							break;
						default:
							break;
						}

						final ArrayList<Term> values = new ArrayList<>();
						values.add(value);
						programStates.put(variable.getTerm(), values);
						break;
					}
				}
			}
			final ProgramState<Term> ps = new ProgramState<>(programStates, Term.class);
			partialProgramStateMapping.put((int) (sequenceNumber - 1), ps);
		}

		return IcfgProgramExecution.create(edges, partialProgramStateMapping);

	}

	public BtorScript generateScript(final IIcfg<BoogieIcfgLocation> icfg) {
		final BtorExpression pcUpdate = generatePCUpdateExpression();
		final Set<BoogieIcfgLocation> initial = icfg.getInitialNodes();
		if (initial.size() != 1) {
			throw new UnsupportedOperationException("Multiple initial states");
		}
		final BtorExpression initial_pc =
				pcMap.get(new SuffixedDebugIdentifier(initial.iterator().next().getDebugIdentifier(),
						initial.iterator().next().getProcedure()));
		final BtorExpression pc_initialization =
				new BtorExpression(new BtorSort(64), BtorExpressionType.INIT, Arrays.asList(pcExpression, initial_pc));
		final List<BtorExpression> variableUpdateExpressions = generateVariableUpdateExpressions();
		final List<BtorExpression> allTopLevelExpressions =
				new ArrayList<>(Arrays.asList(initial_pc, pc_initialization, pcUpdate));
		final List<BtorExpression> badExpressions = generateBadExpressions();
		allTopLevelExpressions.addAll(variableUpdateExpressions);
		allTopLevelExpressions.addAll(badExpressions);
		final Set<BtorSort> sorts = new HashSet<>();
		for (final BtorExpression var : variableMap.values()) {
			sorts.add(var.getSort());

		}
		sorts.add(new BtorSort(1));
		sorts.add(new BtorSort(64));
		return new BtorScript(allTopLevelExpressions, new ArrayList<>(sorts));
	}

}
