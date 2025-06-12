package de.uni_freiburg.informatik.ultimate.reqtotest.testgenerator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.AuxVarGen;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.ReqGraphAnnotation;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.ReqGraphOracleAnnotation;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.Req2TestReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqGuardGraph;

public class TestGeneratorResult implements IResult {

	private final List<SystemState> mTestStates;
	private final List<List<ReqGraphAnnotation>> mStepsAnnotations;
	private final List<Map<ReqGuardGraph, DirectTriggerDependency>> mDependenciesGraphNodes = new ArrayList<>();
	private final AuxVarGen mAuxVarGen;
	private final Req2TestReqSymbolTable mReqSymbolTable;
	private final ReqGraphOracleAnnotation mOracleAnnotation;

	public TestGeneratorResult(final ILogger logger, final List<SystemState> testStates,
			final List<List<ReqGraphAnnotation>> stepsAnnotations, final ReqGraphOracleAnnotation oracleAnnotation,
			final Req2TestReqSymbolTable reqSymbolTable, final AuxVarGen auxVarGen) {
		mTestStates = testStates;
		mStepsAnnotations = stepsAnnotations;
		mAuxVarGen = auxVarGen;
		mReqSymbolTable = reqSymbolTable;
		mOracleAnnotation = oracleAnnotation;
		calculateDependencyGraph();
	}

	private void calculateDependencyGraph() {
		Map<ReqGuardGraph, DirectTriggerDependency> stepDependencyNodes;
		Map<ReqGuardGraph, DirectTriggerDependency> lastStepDependencyNodes = new HashMap<>();
		for (final List<ReqGraphAnnotation> stepAnnotations : mStepsAnnotations) {
			stepDependencyNodes = calculateDependencyGraphStep(stepAnnotations, lastStepDependencyNodes);
			mDependenciesGraphNodes.add(stepDependencyNodes);
			lastStepDependencyNodes = stepDependencyNodes;
		}

	}

	/*
	 * Calculate relations between Requirements in one test step. A relation looks like req1 ---- var1,var2 ----> req2,
	 * read as req2's trigger vars depend on effects var1, var2 set by req1.
	 */
	private Map<ReqGuardGraph, DirectTriggerDependency> calculateDependencyGraphStep(
			final List<ReqGraphAnnotation> stepAnnotations,
			final Map<ReqGuardGraph, DirectTriggerDependency> lastStepDependencies) {
		// initialize dependency nodes: each requirement is represented by a node (in each test step)
		final Map<ReqGuardGraph, DirectTriggerDependency> stepDependencyNodes = new HashMap<>();
		for (final ReqGraphAnnotation annotation : stepAnnotations) {
			final ReqGuardGraph reqAut = annotation.getRequirementAut();
			final DirectTriggerDependency dependencyNode = new DirectTriggerDependency(reqAut);
			stepDependencyNodes.put(reqAut, dependencyNode);
		}
		// for a requirement find an effect that is responsible for triggering the requirement
		for (final ReqGraphAnnotation annotation : stepAnnotations) {
			final DirectTriggerDependency dependencyNode = stepDependencyNodes.get(annotation.getRequirementAut());
			connectEffectDependencies(dependencyNode, stepDependencyNodes, annotation, stepAnnotations);
			connectInputDependencies(dependencyNode, annotation);
			connectOutput(dependencyNode, annotation);
			connectInterStepDependency(dependencyNode, lastStepDependencies, annotation);
		}
		return stepDependencyNodes;
	}

	private void connectInterStepDependency(final DirectTriggerDependency dependencyNode,
			final Map<ReqGuardGraph, DirectTriggerDependency> lastStepDependencyNodes,
			final ReqGraphAnnotation toJustifyAnnotation) {
		if (toJustifyAnnotation.getSourceLocation().getLabel() > 0) {
			// if source.label > 0 there must have already been a useful transition in the last step.
			final DirectTriggerDependency lastStepDepNode =
					lastStepDependencyNodes.get(toJustifyAnnotation.getRequirementAut());
			dependencyNode.connectOutgoing(lastStepDepNode,
					new HashSet<>(Arrays.asList(toJustifyAnnotation.getLabel().getClockGuard().getFreeVars())));
		}
	}

	private void connectEffectDependencies(final DirectTriggerDependency dependencyNode,
			final Map<ReqGuardGraph, DirectTriggerDependency> stepDependencyNodes,
			final ReqGraphAnnotation toJustifyAnnotation, final List<ReqGraphAnnotation> stepAnnotations) {
		final Set<TermVariable> varsToJustify = SmtUtils.getFreeVars(Arrays.asList(toJustifyAnnotation.getGuard()));
		for (final ReqGraphAnnotation annotation : stepAnnotations) {
			if (annotation == toJustifyAnnotation || !annotation.getLabel().isEffect()) {
				continue;
			}
			final Set<TermVariable> varsJustifyable = SmtUtils.getFreeVars(Arrays.asList(annotation.getGuard()));
			varsJustifyable.retainAll(mAuxVarGen.getEffectVariables(annotation.getRequirementAut()));
			final HashSet<TermVariable> justifications = new HashSet<>(varsToJustify);
			justifications.retainAll(varsJustifyable);
			if (justifications.size() > 0) {
				final DirectTriggerDependency justifyingReqNode =
						stepDependencyNodes.get(annotation.getRequirementAut());
				dependencyNode.connectOutgoing(justifyingReqNode, justifications);
			}

		}
	}

	private void connectInputDependencies(final DirectTriggerDependency dependencyNode,
			final ReqGraphAnnotation toJustifyAnnotation) {
		final Set<TermVariable> varsToJustify = SmtUtils.getFreeVars(Arrays.asList(toJustifyAnnotation.getGuard()));
		final Set<String> inputVariables = mReqSymbolTable.getInputVars();
		final Set<TermVariable> justifyingInputs = new HashSet<>();
		for (final TermVariable var : varsToJustify) {
			if (inputVariables.contains(var.getName())) {
				justifyingInputs.add(var);
			}
		}
		dependencyNode.addInputs(justifyingInputs);
	}

	private void connectOutput(final DirectTriggerDependency dependencyNode,
			final ReqGraphAnnotation toJustifyAnnotation) {
		if (!toJustifyAnnotation.getLabel().isEffect()) {
			return;
		}
		final Set<TermVariable> varsToJustify = SmtUtils.getFreeVars(Arrays.asList(toJustifyAnnotation.getGuard()));
		final Collection<TermVariable> effectsOfReq =
				mAuxVarGen.getEffectVariables(toJustifyAnnotation.getRequirementAut());
		final Set<String> outputVariables = mReqSymbolTable.getOutputVars();
		final Set<TermVariable> outputs = new HashSet<>();
		for (final TermVariable var : varsToJustify) {
			if (outputVariables.contains(var.getName()) && effectsOfReq.contains(var)) {
				outputs.add(var);
			}
		}
		dependencyNode.addOutputs(outputs);
	}

	@Override
	public String getPlugin() {
		return null;
	}

	@Override
	public String getShortDescription() {
		return toString();
	}

	@Override
	public String getLongDescription() {
		final StringBuilder sb = new StringBuilder();

		sb.append("Test Vector:" + System.getProperty("line.separator"));

		final Set<DirectTriggerDependency> testNodes = getOracleReverseWalkTestPlan();
		// TODO: Using the test nodes as a filter for the old test generation is just a hack.
		// The resulting nodes edges should be unrolled to generate the test plan by themselves.
		sb.append(getStepsTestPlan(testNodes));
		return sb.toString();
	}

	private Set<DirectTriggerDependency> getOracleReverseWalkTestPlan() {
		final Set<DirectTriggerDependency> oracleDepNodes = getOracleDependencyNodes();
		final Set<DirectTriggerDependency> testNodes = reverseTraverseDependencyGraph(oracleDepNodes);
		return testNodes;
	}

	private Set<DirectTriggerDependency> getOracleDependencyNodes() {
		final Map<ReqGuardGraph, DirectTriggerDependency> stepDependencyNodes =
				mDependenciesGraphNodes.get(mDependenciesGraphNodes.size() - 1);
		final Set<DirectTriggerDependency> outputNodes = new HashSet<>();
		for (final DirectTriggerDependency depNode : stepDependencyNodes.values()) {
			if (!Collections.disjoint(depNode.getOutputs(), mOracleAnnotation.getOracleVars())) {
				outputNodes.add(depNode);
			}
		}
		return outputNodes;
	}

	private Set<DirectTriggerDependency>
			reverseTraverseDependencyGraph(final Set<DirectTriggerDependency> outputNodes) {
		final Set<DirectTriggerDependency> dependencyNodes = new HashSet<>();
		final Queue<DirectTriggerDependency> queue = new LinkedList<>(outputNodes);
		while (!queue.isEmpty()) {
			final DirectTriggerDependency peek = queue.poll();
			dependencyNodes.add(peek);
			for (final DirectTriggerDependency determinesPeek : peek.getOutgoingNodes()) {
				// there may be loops in the dependency graph (think a -> b, b -> a) so prevent unrolling)
				if (!queue.contains(determinesPeek) && !dependencyNodes.contains(determinesPeek)) {
					queue.add(determinesPeek);
				}
			}
		}
		return dependencyNodes;
	}

	private String getStepsTestPlan(final Set<DirectTriggerDependency> filter) {
		final StringBuilder sb = new StringBuilder();
		for (int step = 0; step < mDependenciesGraphNodes.size(); step++) {
			final SystemState state = mTestStates.get(step);
			final float timeStep = mTestStates.get(step).getTimeStep();
			sb.append(System.getProperty("line.separator"));
			final Map<ReqGuardGraph, DirectTriggerDependency> stepDependencyGraphNodes =
					mDependenciesGraphNodes.get(step);
			sb.append(getStepTestPlan(stepDependencyGraphNodes, state, filter, timeStep));
		}
		sb.append("------------------------------------------------------------------------------------------");
		return sb.toString();
	}

	private String getStepTestPlan(final Map<ReqGuardGraph, DirectTriggerDependency> stepDependencyGraphNodes,
			final SystemState state, final Set<DirectTriggerDependency> filter, final float timeStep) {
		final StringBuilder sbin = new StringBuilder();
		final StringBuilder sbout = new StringBuilder();
		sbin.append("Set inputs:");
		sbin.append(System.getProperty("line.separator"));
		for (final DirectTriggerDependency dependencyNode : stepDependencyGraphNodes.values()) {
			if (!filter.contains(dependencyNode)) {
				continue;
			}
			// inputs
			if (dependencyNode.getInputs().size() > 0) {
				sbin.append("\t");
				sbin.append(state.getVarSetToValueSet(dependencyNode.getInputs()));
				sbin.append("\t\t(" + dependencyNode.getReqAut().getName() + ") ");
				sbin.append(System.getProperty("line.separator"));
			}
			// Outputs
			if (dependencyNode.getOutputs().size() > 0) {
				sbout.append("\t");
				sbout.append(state.getVarSetToValueSet(dependencyNode.getOutputs()));
				sbout.append("\t\t(" + dependencyNode.getReqAut().getName() + ") ");
				sbout.append(System.getProperty("line.separator"));
			}
		}
		if (sbout.length() > 0) {
			sbin.append("Expect output:" + System.getProperty("line.separator"));
			sbout.append("Wait exactly  " + Float.toString(timeStep) + System.getProperty("line.separator"));
			return sbin.append(sbout).toString();
		} else {
			sbin.append("Wait exactly  " + Float.toString(timeStep));
			sbin.append(System.getProperty("line.separator"));
			return sbin.toString();
		}

	}

	@SuppressWarnings("unused")
	private String getStepTestPlanGraphed(final Map<ReqGuardGraph, DirectTriggerDependency> stepDependencyGraphNodes,
			final SystemState state, final Set<DirectTriggerDependency> filter, final double timeStep) {
		final StringBuilder sbin = new StringBuilder();
		final StringBuilder sbtrans = new StringBuilder();
		final StringBuilder sbout = new StringBuilder();
		for (final ReqGuardGraph reqAut : stepDependencyGraphNodes.keySet()) {
			final DirectTriggerDependency dependencyNode = stepDependencyGraphNodes.get(reqAut);
			if (!filter.contains(dependencyNode)) {
				continue;
			}
			// inputs
			if (dependencyNode.getInputs().size() > 0) {
				sbin.append("Input ---------- (");
				sbin.append(state.getVarSetToValueSet(dependencyNode.getInputs()));
				sbin.append(") ----------> ");
				sbin.append(dependencyNode.getReqAut().getName());
				sbin.append(System.getProperty("line.separator"));
			}
			// direct trigger dep.
			for (final DirectTriggerDependency dependeeNode : dependencyNode.getOutgoingNodes()) {
				if (dependencyNode.getOutgoingEdgeLabel(dependeeNode).size() > 0) {
					sbtrans.append(dependeeNode.getReqAut().getName());
				} else {
					continue;
				}
				sbtrans.append("---------- (");
				sbtrans.append(state
						.getVarSetToValueSet((Set<TermVariable>) dependencyNode.getOutgoingEdgeLabel(dependeeNode)));
				// sbtrans.append(dependencyNode.getOutgoingEdgeLabel(dependeeNode));
				sbtrans.append(") ----------> ");
				sbtrans.append(dependencyNode.getReqAut().getName());
				sbtrans.append(System.getProperty("line.separator"));
			}
			// Outputs
			if (dependencyNode.getOutputs().size() > 0) {
				sbout.append(dependencyNode.getReqAut().getName());
				sbout.append("---------- (");
				sbout.append(state.getVarSetToValueSet(dependencyNode.getOutputs()));
				sbout.append(") ----------> Output");
				sbout.append(System.getProperty("line.separator"));
			}
		}
		return "Wait " + Double.toString(timeStep) + ":\n" + sbin.append(sbtrans).append(sbout).toString();
	}

	@Override
	public String toString() {
		return String.format("Found Test for: %s", mOracleAnnotation.getOracleVars());
	}

}
