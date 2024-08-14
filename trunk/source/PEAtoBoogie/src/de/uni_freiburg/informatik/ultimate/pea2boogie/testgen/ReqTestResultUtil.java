package de.uni_freiburg.informatik.ultimate.pea2boogie.testgen;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;

public class ReqTestResultUtil {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final IReqSymbolTable mReqSymbolTable;
	private final Map<PhaseEventAutomata, ReqEffectStore> mReqEffectStore;

	public ReqTestResultUtil(final ILogger logger, final IUltimateServiceProvider services,
			final IReqSymbolTable reqSymbolTable, final Map<PhaseEventAutomata, ReqEffectStore> effectStore) {
		mLogger = logger;
		mServices = services;
		mReqSymbolTable = reqSymbolTable;
		mReqEffectStore = effectStore;
	}

	public IResult convertTraceAbstractionResult(final IResult result) {
		if (result instanceof CounterExampleResult<?, ?, ?>) {
			return getTestSteps((CounterExampleResult<?, ?, ?>) result);
		}
		if (result instanceof TimeoutResultAtElement<?> || result instanceof PositiveResult<?>) {
			// TODO
		}
		return result;
	}

	private IResult getTestSteps(final CounterExampleResult<?, ?, ?> result) {
		final List<TestStep> testSteps = new ArrayList<>();
		@SuppressWarnings("unchecked")
		final IProgramExecution<?, Expression> translatedPe = (IProgramExecution<?, Expression>) mServices
				.getBacktranslationService().translateProgramExecution(result.getProgramExecution());
		final AtomicTraceElement<?> finalElement = translatedPe.getTraceElement(translatedPe.getLength() - 1);
		ProgramState<Expression> recentProgramState = null;

		final List<ProgramState<Expression>> states = new ArrayList<>();
		for (int i = 0; i < translatedPe.getLength(); i++) {
			if (translatedPe.getProgramState(i) != null) {
				recentProgramState = translatedPe.getProgramState(i);
			}
			final AtomicTraceElement<?> ate = translatedPe.getTraceElement(i);
			if (ate.getStep() == finalElement.getStep()) {
				if (recentProgramState == null) {
					mLogger.error(
							"Assertion did not contain state (but would have been neccessary for test generation):"
									+ ate.getStep().toString());
					continue;
				}
				states.add(recentProgramState);
				recentProgramState = null;
			}
		}
		for (int i = 0; i < states.size() - 1; i++) {
			testSteps.add(
					getTestStepGraph(calcualteGraphStep(mReqEffectStore.keySet(), states.get(i), states.get(i + 1)),
							states.get(i), states.get(i + 1)));
		}
		// decide if last state is necessary
		// TODO: do that using annotations on the assertions
		final TestStep lastStep =
				getTestStepGraph(
						calcualteGraphStep(mReqEffectStore.keySet(), states.get(states.size() - 1),
								states.get(states.size() - 1)),
						states.get(states.size() - 1), states.get(states.size() - 1));
		if (lastStep.hasOutput()) {
			testSteps.add(lastStep);
		}
		return new ReqTestResultTest(testSteps, getTestAssertionName(finalElement.getStep()));
	}

	public static class TestRelationNode {

		private final PhaseEventAutomata mReq;
		private final Set<PhaseEventAutomata> mDetermined;
		private final Set<String> mVarName;
		private final Set<String> mInputs;
		private final Set<String> mOutputs;
		private final boolean mIsBoundResponse;
		// TODO: store time bound

		/*
		 * Describes a reqirement "req" determining variables "varName" for requirements "determined" and outputs "out"
		 * using inputs "in"
		 */
		public TestRelationNode(final PhaseEventAutomata req, final Set<String> varName, final Set<String> inputs,
				final Set<String> outputs, final boolean boundResponse) {
			mReq = req;
			mVarName = varName;
			mDetermined = new HashSet<>();
			mInputs = inputs;
			mOutputs = outputs;
			mIsBoundResponse = boundResponse;

		}

		public void addDeterminedReq(final PhaseEventAutomata d) {
			mDetermined.add(d);
		}

		public Set<String> getOutputs() {
			return mOutputs;
		}

		public Set<PhaseEventAutomata> getDetermined() {
			return mDetermined;
		}

		public PhaseEventAutomata getReq() {
			return mReq;
		}

		public Set<String> getInputs() {
			return mInputs;
		}

		public boolean isBoundResponse() {
			return mIsBoundResponse;
		}

		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder();
			sb.append(mInputs.toString());
			sb.append("--input-->");
			sb.append(mReq.getName());
			if (mIsBoundResponse) {
				sb.append(" -<><><><>-internal-(");
			} else {
				sb.append(" ----------internal-(");
			}
			sb.append(mVarName.toString());
			sb.append(" )--------output-( ");
			sb.append(mOutputs.toString());
			sb.append(" )---------------> ");
			sb.append(mDetermined.toString());
			sb.append("\n");
			return sb.toString();
		}

	}

	private Map<PhaseEventAutomata, TestRelationNode> calcualteGraphStep(final Set<PhaseEventAutomata> peas,
			final ProgramState<Expression> programState, final ProgramState<Expression> successorState) {
		final Map<PhaseEventAutomata, TestRelationNode> edges = new HashMap<>();
		// loop over all non-upper reqs, everything except the dependees is in the resultedge and pc information
		for (final PhaseEventAutomata pea : peas) {
			final Collection<Expression> pcs = getVariableValuation(mReqSymbolTable.getPcName(pea), programState);
			// get current location index of the pea
			final Expression[] pca = pcs.toArray(new Expression[pcs.size()]);
			final int pc = Integer.parseInt(((IntegerLiteral) pca[0]).getValue()); // TODO: validation
			if (pc < pea.getPhases().size() / 2) {
				// automaton is in its upper half, so it does not set anything
				continue;
			}
			// get phase invariant and all variables therein
			final CDD invar = pea.getPhases().get(pc).getStateInvariant();
			final Set<String> vars = Req2CauseTrackingCDD.getCddVariables(invar);
			Set<String> effectVars = Collections.emptySet();
			Set<String> determinedOutputs = Collections.emptySet();
			if (isInEffectPhase(pea, programState)) {
				// remove effects if pea is in effect phase
				vars.removeAll(mReqEffectStore.get(pea).getEffectVars());
				effectVars = mReqEffectStore.get(pea).getEffectVars();
				determinedOutputs = mReqEffectStore.get(pea).getEffectVars();
				determinedOutputs.retainAll(mReqSymbolTable.getOutputVars());

			}
			if (endsInEffectEdge(pea, successorState)) {
				// note effect neccesary for next phase
				effectVars = mReqEffectStore.get(pea).getEffectVars();
				determinedOutputs = mReqEffectStore.get(pea).getEffectVars();
				determinedOutputs.retainAll(mReqSymbolTable.getOutputVars());

			}
			final Set<String> requiredInputs = Req2CauseTrackingCDD.getCddVariables(invar);
			requiredInputs.retainAll(mReqSymbolTable.getInputVars());
			edges.put(pea,
					new TestRelationNode(pea, effectVars, requiredInputs, determinedOutputs,
							!mReqEffectStore.get(pea).getEffectEdges().isEmpty()
									&& mReqEffectStore.get(pea).getEffectPhaseIndexes().isEmpty()));
		}
		// connect to requirements determining internal variables
		for (final PhaseEventAutomata pea : peas) {
			final Collection<Expression> pcs = getVariableValuation(mReqSymbolTable.getPcName(pea), programState);
			// get current location index of the pea
			final Expression[] pca = pcs.toArray(new Expression[pcs.size()]);
			final int pc = Integer.parseInt(((IntegerLiteral) pca[0]).getValue()); // TODO: validation
			if (pc < pea.getPhases().size() / 2) {
				// automaton is in its upper half, so it does not use anything
				continue;
			}
			// get phase invariant and all variables therein
			final CDD invar = pea.getPhases().get(pc).getStateInvariant();
			final Set<String> vars = Req2CauseTrackingCDD.getCddVariables(invar);
			if (isInEffectPhase(pea, programState)) {
				// remove effects if pea is in effect phase
				vars.removeAll(mReqEffectStore.get(pea).getEffectVars());
			}
			vars.removeAll(mReqSymbolTable.getConstVars());
			vars.removeAll(mReqSymbolTable.getInputVars());
			// build up graph connections
			for (final String var : vars) {
				calculateDeterminingReqs(var, programState).stream().forEach(d -> edges.get(d).addDeterminedReq(pea));
				calculateEntryEffects(var, successorState).stream().forEach(d -> edges.get(d).addDeterminedReq(pea));
			}
		}
		mLogger.info(edges);
		return edges;
	}

	/*
	 * Calculates the set of requirements that determine the value of a given variable varName in the automaton
	 * configuration given by the current program state.
	 */
	private Set<PhaseEventAutomata> calculateDeterminingReqs(final String varName,
			final ProgramState<Expression> programState) {
		// TODO return accodring node of graph here (req1, v, req2) read "req1 enables req2 by setting v"
		final Set<PhaseEventAutomata> determiners = new HashSet<>();
		for (final Entry<PhaseEventAutomata, ReqEffectStore> entry : mReqEffectStore.entrySet()) {
			final ReqEffectStore reqEffectStore = entry.getValue();
			if (!reqEffectStore.getEffectVars().contains(varName)) {
				continue;
			}
			if (isInEffectPhase(entry.getKey(), programState)) {
				determiners.add(entry.getKey());
			}
		}
		return determiners;
	}

	/*
	 * True if the pea is in an effect phase (any location including the highest phase) in the given program state.
	 */
	private boolean isInEffectPhase(final PhaseEventAutomata pea, final ProgramState<Expression> programState) {
		final ReqEffectStore store = mReqEffectStore.get(pea);
		if (store == null) {
			return false;
		}
		final String pcIdent = mReqSymbolTable.getPcName(pea);
		final Collection<Expression> values = getVariableValuation(pcIdent, programState);
		for (final Expression expr : values) {
			if (expr instanceof IntegerLiteral) {
				final int value = Integer.parseInt(((IntegerLiteral) expr).getValue());
				if (store.getEffectPhaseIndexes().contains(value)) {
					return true;
				}
			}
		}
		return false;
	}

	/*
	 * Calculates the set of requirements that will be able to determine the value of variable varName by a bound
	 * response effect.
	 */
	private Set<PhaseEventAutomata> calculateEntryEffects(final String varName,
			final ProgramState<Expression> programState) {
		// TODO return accodring node of graph here (req1, v, req2) read "req1 enables req2 by setting v"
		final Set<PhaseEventAutomata> determiners = new HashSet<>();
		for (final Entry<PhaseEventAutomata, ReqEffectStore> entry : mReqEffectStore.entrySet()) {
			final ReqEffectStore reqEffectStore = entry.getValue();
			if (!reqEffectStore.getEffectVars().contains(varName)) {
				continue;
			}
			if (endsInEffectEdge(entry.getKey(), programState)) {
				determiners.add(entry.getKey());
			}
		}
		return determiners;
	}

	/*
	 * True if the pea just took a transition over an effect transition (any transition leaving a highest waiting phase)
	 * i.e. the effect variables are determined by the requirements effect in this program state.
	 */
	private boolean endsInEffectEdge(final PhaseEventAutomata pea, final ProgramState<Expression> programState) {
		final ReqEffectStore store = mReqEffectStore.get(pea);
		if (store == null) {
			return false;
		}
		final String pcIdent = mReqSymbolTable.getPcName(pea);
		final Collection<Expression> pcValues = getVariableValuation(pcIdent, programState);
		final String primePcIdent = mReqSymbolTable.getHistoryVarId(mReqSymbolTable.getPcName(pea));
		final Collection<Expression> primePcValues = getVariableValuation(primePcIdent, programState);
		for (final Expression exprPrime : primePcValues) {
			final int valuePrimePc = Integer.parseInt(((IntegerLiteral) exprPrime).getValue());
			for (final Expression expr : pcValues) {
				final int valuePc = Integer.parseInt(((IntegerLiteral) expr).getValue());
				if (store.getEffectEdges().stream()
						.filter(e -> e.getFirst() == valuePrimePc && e.getSecond() == valuePc).count() > 0) {
					return true;
				}
			}
		}
		return false;
	}

	private TestStep getTestStepGraph(final Map<PhaseEventAutomata, TestRelationNode> edges,
			final ProgramState<Expression> programState, final ProgramState<Expression> successorState) {
		final Collection<TestRelationNode> testRelations = edges.values();
		// set of edges to be used: get outputs, add edges as long as there are pending internal vars
		// TODO: fix this part: correctly figure out what the dependencies are
		final Collection<TestRelationNode> reqsInThisTestStep = testRelations;
		/*
		 * final Set<TestRelationNode> reqsInThisTestStep = testRelations.stream().filter(edge ->
		 * !edge.getOutputs().isEmpty()).collect(Collectors.toSet()); final LinkedList<PhaseEventAutomata> queue = new
		 * LinkedList<>(); queue.addAll(testRelations.stream().filter(edge -> !edge.getOutputs().isEmpty()).map(edge ->
		 * edge.getReq()).collect(Collectors.toList())); final Set<PhaseEventAutomata> done = new HashSet<>();
		 * while(!queue.isEmpty()) { final PhaseEventAutomata element = queue.pop(); done.add(element);
		 * reqsInThisTestStep.addAll(testRelations.stream().filter(e ->
		 * e.getDetermined().contains(element)).collect(Collectors.toSet()));
		 * queue.addAll(testRelations.stream().filter(e -> e.getDetermined().contains(element)).map(e ->
		 * e.getReq()).collect(Collectors.toSet())); }
		 */

		Collection<Expression> waitForTime = new ArrayList<>();
		final Map<IdentifierExpression, Collection<Expression>> inputAssignment = new HashMap<>();
		final Map<IdentifierExpression, Collection<Expression>> outputAssignment = new HashMap<>();
		final Map<IdentifierExpression, Collection<Expression>> waitAssignment = new HashMap<>();
		final Set<String> outVars = new HashSet<>();
		final Set<String> waitVars = new HashSet<>();
		final Set<String> inVars = new HashSet<>();
		for (final TestRelationNode step : reqsInThisTestStep) {
			if (step.isBoundResponse()) {
				// TODO: or if the req is determined by a waiting req...
				waitVars.addAll(step.getOutputs());
			} else {
				outVars.addAll(step.getOutputs());
			}
			inVars.addAll(step.getInputs());
		}
		for (final Expression exp : programState.getVariables()) {
			final String ident = ((IdentifierExpression) exp).getIdentifier();
			if (exp instanceof IdentifierExpression && inVars.contains(ident)) {
				inputAssignment.put((IdentifierExpression) exp, programState.getValues(exp));
			}
			if (exp instanceof IdentifierExpression && mReqSymbolTable.getDeltaVarName().equals(ident)) {
				waitForTime = programState.getValues(exp);
			}
			if (exp instanceof IdentifierExpression && outVars.contains(ident)) {
				outputAssignment.put((IdentifierExpression) exp, programState.getValues(exp));
			}
		}
		for (final Expression exp : successorState.getVariables()) {
			final String ident = ((IdentifierExpression) exp).getIdentifier();
			if (exp instanceof IdentifierExpression && waitVars.contains(ident)) {
				waitAssignment.put((IdentifierExpression) exp, successorState.getValues(exp));
			}
		}
		return new TestStep(inputAssignment, outputAssignment, waitAssignment, waitForTime);
	}

	private TestStep getTestStep(final ProgramState<Expression> programState) {
		final Map<IdentifierExpression, Collection<Expression>> inputAssignment = new HashMap<>();
		final Map<IdentifierExpression, Collection<Expression>> outputAssignment = new HashMap<>();
		Collection<Expression> waitForTime = new ArrayList<>();
		for (final Expression exp : programState.getVariables()) {
			final String ident = ((IdentifierExpression) exp).getIdentifier();
			if (exp instanceof IdentifierExpression && mReqSymbolTable.getInputVars().contains(ident)) {
				inputAssignment.put((IdentifierExpression) exp, programState.getValues(exp));
			} else if (exp instanceof IdentifierExpression && mReqSymbolTable.getDeltaVarName().equals(ident)) {
				waitForTime = programState.getValues(exp);
			} else if (exp instanceof IdentifierExpression && mReqSymbolTable.getOutputVars().contains(ident)
					&& isSetByEffect(ident, programState)) {
				outputAssignment.put((IdentifierExpression) exp, programState.getValues(exp));
			}

		}
		return new TestStep(inputAssignment, outputAssignment, Collections.emptyMap(), waitForTime);
	}

	private static Collection<Expression> getVariableValuation(final String varName,
			final ProgramState<Expression> programState) {
		final Expression identExpr = programState.getVariables().stream()
				.filter(v -> ((IdentifierExpression) v).getIdentifier().equals(varName)).findFirst().orElse(null);
		if (identExpr == null) {
			return Collections.emptySet();
		}
		return programState.getValues(identExpr);
	}

	private boolean isSetByEffect(final String ident, final ProgramState<Expression> programState) {
		final String trackingVar = ReqTestAnnotator.getTrackingVar(ident);
		for (final Expression identExpr : programState.getVariables()) {
			if (((IdentifierExpression) identExpr).getIdentifier().equals(trackingVar)) {
				for (final Expression expr : programState.getValues(identExpr)) {
					if (expr instanceof BooleanLiteral) {
						return ((BooleanLiteral) expr).getValue();
					}
					mLogger.error("Unsuspected Value for tracking Variable for var: " + ident);
				}
			}
		}
		return false;
	}

	private static String getTestAssertionName(final Object e) {
		if (e instanceof AssertStatement) {
			final NamedAttribute[] attrs = ((AssertStatement) e).getAttributes();
			if (attrs != null && attrs.length > 0) {
				for (final NamedAttribute attr : attrs) {
					if (attr.getName().startsWith(ReqTestAnnotator.TEST_ASSERTION_PREFIX)) {
						return attr.getName();
					}
				}
			}
		}
		return "None";
	}

}
