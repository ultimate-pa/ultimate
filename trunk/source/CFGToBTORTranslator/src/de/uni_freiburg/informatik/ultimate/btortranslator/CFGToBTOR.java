package de.uni_freiburg.informatik.ultimate.btortranslator;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.btor.AssignmentRule;
import de.uni_freiburg.informatik.ultimate.btor.BtorScript;
import de.uni_freiburg.informatik.ultimate.btor.BtorSort;
import de.uni_freiburg.informatik.ultimate.btor.UpdateRule;
import de.uni_freiburg.informatik.ultimate.btor.expression.AndExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.BtorExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.ConstdExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.EqExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.ITEExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.StateExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.UlteExpression;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.lib.icfg.BoogieIcfgLocation;
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
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class CFGToBTOR {
	// Variable and the corresponding btor expression that initializes it
	private final HashMap<String, StateExpression> variableMap;
	// Set of update rules from each location
	private final HashMap<SuffixedDebugIdentifier, List<UpdateRule>> locationUpdateMap;
	// Set of assignments for each variable
	private final HashMap<String, List<AssignmentRule>> variableAssignmentMap;
	// Set of all icfg locations
	private Map<String, Map<DebugIdentifier, BoogieIcfgLocation>> allLocations;
	// Set of all icfg error locations
	private final Set<DebugIdentifier> errorLocations;
	// Btor expressions containing possible pc transitions from each location
	private final Map<SuffixedDebugIdentifier, BtorExpression> pcMap;
	// Btor expression for the program counter
	private final StateExpression pcExpression;
	private final List<BtorExpression> constraintExpressions;
	ManagedScript mScript;
	IUltimateServiceProvider mService;/////
	private final Boogie2SMT boogie2SMT;
	BtorScript btorScript;

	public CFGToBTOR(final ManagedScript mScript, final IUltimateServiceProvider service, final Boogie2SMT boogie2SMT) {
		this.mScript = mScript;
		mService = service;
		btorScript = new BtorScript();
		variableMap = new HashMap<>();
		locationUpdateMap = new HashMap<>();
		errorLocations = new HashSet<>();
		variableAssignmentMap = new HashMap<>();
		pcMap = new HashMap<>();
		pcExpression = btorScript.createStateExpression(new BtorSort(64), "pc");
		constraintExpressions = new ArrayList<>();
		this.boogie2SMT = boogie2SMT;
	}

	// For each variable, create a corresponding btor expression.
	public void extractVariables(final IIcfg<BoogieIcfgLocation> icfg) {
		final Set<IProgramVar> allVariables = IcfgUtils.collectAllProgramVars(icfg.getCfgSmtToolkit());
		for (final IProgramVar var : allVariables) {
			final BtorSort sort = new BtorSort(var.getSort());
			final StateExpression newState = btorScript.createStateExpression(sort, var.getGloballyUniqueId());
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
				// Extract transition formula and guard from each outgoing edge to generate the update rules for
				// variables present in the transition formula.
				for (final IcfgEdge edge : outgoing) {

					final UnmodifiableTransFormula transitionFormula = edge.getTransformula();
					final Term guard =
							TransFormulaUtils.computeGuard(transitionFormula, mScript, mService).getFormula();
					updateRules.add(
							new UpdateRule(guard, new SuffixedDebugIdentifier(edge.getTarget().getDebugIdentifier(),
									edge.getTarget().getProcedure()), transitionFormula, edge, btorScript));
				}
				locationUpdateMap.put(new SuffixedDebugIdentifier(debugIdentifier, procedure), updateRules);
			}
		}
	}

	public void extractBadStates(final IIcfg<BoogieIcfgLocation> icfg) {
		// Collect suffixed debug identifiers of all icfg error locations.
		for (final BoogieIcfgLocation errorLocation : IcfgUtils.getErrorLocations(icfg)) {
			errorLocations
					.add(new SuffixedDebugIdentifier(errorLocation.getDebugIdentifier(), errorLocation.getProcedure()));
		}
	}

	private void generateAssignments(final DebugIdentifier location, final TransFormula tf, final IcfgEdge icfgEdge,
			final BtorExpression guard) {

		// Get list of assignment rules from edge
		final List<AssignmentRule> assignments =
				AssignmentRule.getAssignmentsFromTransition(location, icfgEdge, guard, boogie2SMT, btorScript);
		for (final AssignmentRule assignment : assignments) {
			// Either get the variable to be assigned or put it into the variable assignment map if it does not already
			// exist.
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
		// PC starts at 1, 0 reserved for unrecoverable state
		int pc = 1;
		// Generate map from location IDs to btor constants
		for (final SuffixedDebugIdentifier locID : locationUpdateMap.keySet()) {
			pcMap.put(locID, btorScript.createConstdExpression(new BtorSort(64), pc));
			System.out.println("locID: " + locID + " pc: " + pc);
			pc++;
		}
		final BtorExpression zero = btorScript.createZeroExpression(new BtorSort(64));
		BtorExpression latestITE = zero;
		// generate next for each location in the form of latest ITE
		for (final SuffixedDebugIdentifier locID : locationUpdateMap.keySet()) {
			BtorExpression latestUpdate = zero;
			final List<UpdateRule> updates = locationUpdateMap.get(locID);
			// checks if we are at the correct line
			final BtorExpression lineCheck =
					btorScript.createBinaryExpression(EqExpression.class, pcExpression, pcMap.get(locID));
			// in the case of only one update, build and return the update btor expression directly
			if (updates.size() == 1) {
				final BtorExpression guard = updates.get(0).getConditionAsExpression(variableMap);
				latestUpdate = btorScript.createTernaryExpression(ITEExpression.class, guard,
						pcMap.get(updates.get(0).getTargetIdentifier()), latestUpdate);
				generateAssignments(locID, updates.get(0).getTransFormula(), updates.get(0).getIcfgEdge(), guard);

			} else if (!updates.isEmpty()) { // multiple updates
				// determine if there are any nondeterministic guards, counting the number of nondet guards in the
				// process
				int nondetEdgesCount = 0;
				boolean detEdgeExists = false;
				final ArrayList<BtorExpression> newGuards = new ArrayList<>();
				final ArrayList<Boolean> isNondet = new ArrayList<>();
				for (final UpdateRule update : updates) {
					if (SmtUtils.isTrueLiteral(update.getCondition())) { // nondet guard
						nondetEdgesCount++;
						isNondet.add(true);
					} else {
						detEdgeExists = true;
						isNondet.add(false);
					}
				}

				int maxInputValue;
				int bitsForInput;
				assert (updates.size() != 0);
				if (detEdgeExists) {
					maxInputValue = nondetEdgesCount + 1;
					bitsForInput = (int) Math.ceil((Math.log(maxInputValue) / Math.log(2)));
				} else {
					maxInputValue = nondetEdgesCount;
					bitsForInput = (int) Math.ceil((Math.log(maxInputValue) / Math.log(2)));
				}

				if (nondetEdgesCount == 0) { // only det guards
					// construct guards normally
					for (final UpdateRule update : updates) {
						final BtorExpression guard = update.getConditionAsExpression(variableMap);
						latestUpdate = btorScript.createTernaryExpression(ITEExpression.class, guard,
								pcMap.get(update.getTargetIdentifier()), latestUpdate);
						generateAssignments(locID, update.getTransFormula(), update.getIcfgEdge(), guard);
					}

				} else { // notdet guards exist, create guards with their corresponding inputs
					final BtorExpression input =
							btorScript.createInputExpression(new BtorSort(bitsForInput), locID + "_input");

					int inputIndex = 0;
					int inputForDeterministicEdges = -1;
					for (int i = 0; i < updates.size(); i++) {
						final UpdateRule update = updates.get(i);
						BtorExpression inputValue;
						if (isNondet.get(i)) {
							inputValue = btorScript.createConstdExpression(new BtorSort(bitsForInput), inputIndex);
							inputIndex++;
						} else {
							if (inputForDeterministicEdges < 0) {
								inputForDeterministicEdges = inputIndex;
								inputIndex++;
							}
							inputValue = btorScript.createConstdExpression(new BtorSort(bitsForInput),
									inputForDeterministicEdges);
						}
						final BtorExpression inputCheck =
								btorScript.createBinaryExpression(EqExpression.class, input, inputValue);
						final BtorExpression guard = btorScript.createBinaryExpression(AndExpression.class,
								update.getConditionAsExpression(variableMap), inputCheck);
						latestUpdate = btorScript.createTernaryExpression(ITEExpression.class, guard,
								pcMap.get(update.getTargetIdentifier()), latestUpdate);
						generateAssignments(locID, update.getTransFormula(), update.getIcfgEdge(), guard);
					}
					final BtorExpression inputLessThanMaxInputValue =
							btorScript.createBinaryExpression(UlteExpression.class, input,
									btorScript.createConstdExpression(new BtorSort(bitsForInput), maxInputValue - 1));
					final BtorExpression inputConstraint =
							btorScript.createConstraintExpression(inputLessThanMaxInputValue);
					constraintExpressions.add(inputConstraint);
				}
			}
			latestITE = btorScript.createTernaryExpression(ITEExpression.class, lineCheck, latestUpdate, latestITE);
		}

		return latestITE;
	}

	// Note: Assume that there are not multiple assignments at the same location to the same variable, with overlapping
	// guard conditions
	private List<BtorExpression> generateVariableUpdateExpressions() {
		final ArrayList<BtorExpression> updateExpressions = new ArrayList<>();
		for (final String var : variableMap.keySet()) {
			final StateExpression varExpression = variableMap.get(var);

			// Base case of ITE chain: variable maps to itself
			BtorExpression lastITE = varExpression;

			// Variable has no assignment
			if (variableAssignmentMap.get(var) == null) {
				final BtorExpression next = btorScript.createNextExpression(varExpression, varExpression);
				updateExpressions.add(next);
				continue;
			}
			for (final AssignmentRule rule : variableAssignmentMap.get(var)) {
				final BtorExpression rhsExpression = rule.getRHSAsExpression(variableMap);
				// Expression that checks if the PC is at the line the assignment takes place
				final BtorExpression lineCheck = btorScript.createBinaryExpression(EqExpression.class, pcExpression,
						pcMap.get(rule.assignmentLocationIdentifier));
				// Assignment only occurs if both PC = assignment location and the guard holds
				final BtorExpression lineAndGuardCheck =
						btorScript.createBinaryExpression(AndExpression.class, lineCheck, rule.guard);
				// Inductive step of adding the assignment
				lastITE = btorScript.createTernaryExpression(ITEExpression.class, lineAndGuardCheck, rhsExpression,
						lastITE);
			}

			final BtorExpression next = btorScript.createNextExpression(varExpression, lastITE);
			updateExpressions.add(next);
		}
		return updateExpressions;
	}

	// generates a list of corresponding bad expressions given the list of error locations
	private List<BtorExpression> generateBadExpressions() {
		final ArrayList<BtorExpression> badExpressions = new ArrayList<>();
		for (final DebugIdentifier errorLocation : errorLocations) {
			final BtorExpression eq =
					btorScript.createBinaryExpression(EqExpression.class, pcExpression, pcMap.get(errorLocation));
			final BtorExpression badExpression = btorScript.createBadExpression(eq);
			badExpressions.add(badExpression);
		}
		return badExpressions;
	}

	public IcfgProgramExecution<IcfgEdge> extractErrorTrace(final IIcfg<BoogieIcfgLocation> icfg,
			final ArrayList<Long> pcList, final Map<Long, Map<String, Long>> programStateSequence) {
		final List<IcfgEdge> edges = new ArrayList<>();
		final List<BoogieIcfgLocation> locs = new ArrayList<>();
		final Map<Long, SuffixedDebugIdentifier> pcToDI = new HashMap<>();

		final boolean multipleInitialStates = icfg.getInitialNodes().size() > 1;

		// Invert PC map, unwrapping the btor expressions
		for (final SuffixedDebugIdentifier ident : pcMap.keySet()) {
			pcToDI.put(((ConstdExpression) pcMap.get(ident)).getConstant(), ident);
		}
		// final Map<DebugIdentifier, BoogieIcfgLocation> diToLoc = icfg.getProgramPoints().values().iterator().next();
		final Map<DebugIdentifier, BoogieIcfgLocation> diToLoc = new HashMap<>();
		final Collection<Map<DebugIdentifier, BoogieIcfgLocation>> programPointMaps = icfg.getProgramPoints().values();

		// Build debug identifier to icfgLocation map
		for (final Map<DebugIdentifier, BoogieIcfgLocation> prodecureLocations : programPointMaps) {
			final Set<DebugIdentifier> keys = prodecureLocations.keySet();
			for (final DebugIdentifier key : keys) {
				final BoogieIcfgLocation loc = prodecureLocations.get(key);
				final SuffixedDebugIdentifier suffixedKey = new SuffixedDebugIdentifier(key, loc.getProcedure());
				diToLoc.put(suffixedKey, prodecureLocations.get(key));
			}
		}

		// Build list of locations visited by error trace parsed from btormc output
		for (final Long pc : pcList) {
			locs.add(diToLoc.get(pcToDI.get((long) pc)));
		}

		// determine outgoing edges taken from each location
		int i = 0;
		if (multipleInitialStates) {
			i = 1;
		}
		for (; i < locs.size() - 1; i++) {
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

		// Build partial state mapping (set of SMT terms) from program states parsed from btormc output
		final Set<IProgramVar> allVariables = IcfgUtils.collectAllProgramVars(icfg.getCfgSmtToolkit());
		final Map<Integer, ProgramState<Term>> partialProgramStateMapping = new HashMap<>();
		for (final long sequenceNumber : programStateSequence.keySet()) {
			if (sequenceNumber == 0 || (multipleInitialStates && sequenceNumber == 1)) { // Ultimate does not care about
																							// initial state
				continue;
			}
			final Map<Term, Collection<Term>> programStates = new HashMap<>();
			final Map<String, Long> assignmentMapping = programStateSequence.get(sequenceNumber);
			for (final String varName : assignmentMapping.keySet()) {
				for (final IProgramVar variable : allVariables) {
					// Convert to smt types
					if (varName.equals(variable.getGloballyUniqueId())) {
						Term value = null;
						switch (variable.getSort().getName()) {
						case "Int":
							value = SmtUtils.constructIntValue(mScript.getScript(),
									BigInteger.valueOf(assignmentMapping.get(varName)));
							break;
						case "Bool":
							if (assignmentMapping.get(varName) == 1) {
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
			final int offset = multipleInitialStates ? 2 : 1;
			partialProgramStateMapping.put((int) (sequenceNumber - offset), ps); // Convert to Ultimate format, 0 ->
																					// program
			// state after one transition
		}

		return IcfgProgramExecution.create(edges, partialProgramStateMapping);

	}

	public BtorScript generateScript(final IIcfg<BoogieIcfgLocation> icfg) {
		BtorExpression pcUpdate = generatePCUpdateExpression();
		final Set<BoogieIcfgLocation> initial = icfg.getInitialNodes();
		if (initial.size() == 0) {
			throw new UnsupportedOperationException("No initial states");
		}
		BtorExpression initial_pc;
		if (initial.size() != 1) {
			// multiple initial states
			// create an initial state that goes to all the initial states

			initial_pc = btorScript.createConstdExpression(new BtorSort(64), Integer.MAX_VALUE);
			final BtorExpression intMax = btorScript.createConstdExpression(new BtorSort(64), Integer.MAX_VALUE);

			final BtorExpression isNewInitialState =
					btorScript.createBinaryExpression(EqExpression.class, pcExpression, intMax);

			final BtorExpression initialpcUpdate =
					btorScript.createInputExpression(new BtorSort(64), "Initial_pc_chooser");

			final BtorExpression zero = btorScript.createZeroExpression(new BtorSort(64));
			BtorExpression latestITE = zero;
			int inputValue = 0;
			for (final BoogieIcfgLocation loc : initial) {
				final BtorExpression inputValueExpression =
						btorScript.createConstdExpression(new BtorSort(64), inputValue);
				final BtorExpression initialpcEquality =
						btorScript.createBinaryExpression(EqExpression.class, inputValueExpression, initialpcUpdate);

				latestITE = btorScript.createTernaryExpression(ITEExpression.class, initialpcEquality,
						pcMap.get(new SuffixedDebugIdentifier(loc.getDebugIdentifier(), loc.getProcedure())),
						latestITE);
				inputValue++;
			}
			final BtorExpression isInitialITE =
					btorScript.createTernaryExpression(ITEExpression.class, isNewInitialState, latestITE, pcUpdate);
			pcUpdate = btorScript.createNextExpression(pcExpression, isInitialITE);
		} else {
			final BtorExpression next = btorScript.createNextExpression(pcExpression, pcUpdate);
			initial_pc = pcMap.get(new SuffixedDebugIdentifier(initial.iterator().next().getDebugIdentifier(),
					initial.iterator().next().getProcedure()));

		}

		final BtorExpression pc_initialization = btorScript.createInitExpression(pcExpression, initial_pc);

		final List<BtorExpression> variableUpdateExpressions = generateVariableUpdateExpressions();

		final List<BtorExpression> badExpressions = generateBadExpressions();

		return btorScript;
	}

}
