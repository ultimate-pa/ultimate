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
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.AuxVarGen;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.ReqGraphAnnotation;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.ReqGraphOracleAnnotation;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqGuardGraph;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqSymbolTable;

public class TestGeneratorResult implements IResult  {
	
	private final List<SystemState> mTestStates;
	private final List<List<ReqGraphAnnotation>> mStepsAnnotations;
	private final List<Map<ReqGuardGraph, DirectTriggerDependency>> mDependenciesGraphNodes = new ArrayList<>();
	private final AuxVarGen mAuxVarGen;
	private final ReqSymbolTable mReqSymbolTable;
	private final ReqGraphOracleAnnotation mOracleAnnotation;
	
	public TestGeneratorResult (ILogger logger, List<SystemState> testStates, List<List<ReqGraphAnnotation>> stepsAnnotations, 
			ReqGraphOracleAnnotation oracleAnnotation, ReqSymbolTable reqSymbolTable, AuxVarGen auxVarGen) {
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
		for(List<ReqGraphAnnotation> stepAnnotations: mStepsAnnotations) {
			stepDependencyNodes = calculateDependencyGraphStep(stepAnnotations, lastStepDependencyNodes);
			mDependenciesGraphNodes.add(stepDependencyNodes);
			lastStepDependencyNodes = stepDependencyNodes;
		}
		
	}
	 
	/*
	 * Calculate relations between Requirements in one test step.
	 * A relation looks like req1 ---- var1,var2 ----> req2, read as req2's trigger vars depend on effects var1, var2 set by req1.
	 */
	private Map<ReqGuardGraph, DirectTriggerDependency> calculateDependencyGraphStep(List<ReqGraphAnnotation> stepAnnotations, 
			Map<ReqGuardGraph, DirectTriggerDependency> lastStepDependencies) {
		//initialize dependency nodes: each requirement is represented by a node (in each test step)
		Map<ReqGuardGraph, DirectTriggerDependency> stepDependencyNodes = new HashMap<>();
		for(ReqGraphAnnotation annotation: stepAnnotations) {
			ReqGuardGraph reqAut = annotation.getRequirementAut();
			DirectTriggerDependency dependencyNode = new DirectTriggerDependency(reqAut);
			stepDependencyNodes.put(reqAut, dependencyNode);
		}
		//for a requirement find an effect that is responsible for triggering the quirement
		for(ReqGraphAnnotation annotation: stepAnnotations) {
			DirectTriggerDependency dependencyNode = stepDependencyNodes.get(annotation.getRequirementAut());
			connectEffectDependencies(dependencyNode, stepDependencyNodes, annotation, stepAnnotations);
			connectInputDependencies(dependencyNode, annotation);
			connectOutput(dependencyNode, annotation);
			connectInterStepDependency(dependencyNode, lastStepDependencies, annotation);
		}
		return stepDependencyNodes;
	}
	
	private void connectInterStepDependency(DirectTriggerDependency dependencyNode, Map<ReqGuardGraph, DirectTriggerDependency> lastStepDependencyNodes,
			ReqGraphAnnotation toJustifyAnnotation) {
		if(toJustifyAnnotation.getSourceLocation().getLabel() > 0) {
			//if source.label > 0 there must have already been a useful transition in the last step.
			DirectTriggerDependency lastStepDepNode = lastStepDependencyNodes.get(toJustifyAnnotation.getRequirementAut());
			dependencyNode.connectOutgoing(lastStepDepNode, new HashSet<TermVariable>());
		}
	}
	
	private void connectEffectDependencies(DirectTriggerDependency dependencyNode, Map<ReqGuardGraph, DirectTriggerDependency> stepDependencyNodes,
			ReqGraphAnnotation toJustifyAnnotation, List<ReqGraphAnnotation> stepAnnotations) {
		Set<TermVariable> varsToJustify = SmtUtils.getFreeVars( Arrays.asList(toJustifyAnnotation.getGuard()) );
		for(ReqGraphAnnotation annotation: stepAnnotations) {
			if(annotation == toJustifyAnnotation || !annotation.getLabel().isEffect()) {
				continue;
			}
			Set<TermVariable> varsJustifyable = SmtUtils.getFreeVars( Arrays.asList(annotation.getGuard()) );
			varsJustifyable.retainAll(mAuxVarGen.getEffectVariables(annotation.getRequirementAut()));
			HashSet<TermVariable> justifications = new HashSet<>(varsToJustify);
			justifications.retainAll(varsJustifyable);
			if (justifications.size() > 0) {
				DirectTriggerDependency justifyingReqNode = stepDependencyNodes.get(annotation.getRequirementAut());
				dependencyNode.connectOutgoing(justifyingReqNode, justifications);
			}
			
		}
	}
	
	private void connectInputDependencies(DirectTriggerDependency dependencyNode, ReqGraphAnnotation toJustifyAnnotation) {
		Set<TermVariable> varsToJustify = SmtUtils.getFreeVars( Arrays.asList(toJustifyAnnotation.getGuard()) );
		Set<String> inputVariables = mReqSymbolTable.getInputVars();
		Set<TermVariable> justifyingInputs = new HashSet<TermVariable>();
		for(TermVariable var: varsToJustify) {
			if(inputVariables.contains(var.getName())) {
				justifyingInputs.add(var);
			}
		}
		dependencyNode.addInputs(justifyingInputs);	
	}
	
	private void connectOutput(DirectTriggerDependency dependencyNode, ReqGraphAnnotation toJustifyAnnotation) {
		if (!toJustifyAnnotation.getLabel().isEffect()) {
			return;
		}
		Set<TermVariable> varsToJustify = SmtUtils.getFreeVars( Arrays.asList(toJustifyAnnotation.getGuard()) );
		Collection<TermVariable> effectsOfReq = mAuxVarGen.getEffectVariables(toJustifyAnnotation.getRequirementAut());
		Set<String> outputVariables = mReqSymbolTable.getOutputVars();
		Set<TermVariable> outputs = new HashSet<TermVariable>(); 
		for(TermVariable var: varsToJustify) {
			if(outputVariables.contains(var.getName()) && effectsOfReq.contains(var)) {
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
		StringBuilder sb = new StringBuilder();
		
		sb.append("Test Vector:"+System.getProperty("line.separator"));
		
		Set<DirectTriggerDependency> testNodes = getOracleReverseWalkTestPlan();
		//TODO: Using the test nodes as a filter for the old test generation is just a hack.
		// The resulting nodes edges should be unrolled to generate the test plan by themselves.
		sb.append(getStepsTestPlan(testNodes));
		return sb.toString();
	}
	
	private Set<DirectTriggerDependency> getOracleReverseWalkTestPlan(){
		Set<DirectTriggerDependency> oracleDepNodes = getOracleDependencyNodes();
		Set<DirectTriggerDependency> testNodes = reverseTraverseDependencyGraph(oracleDepNodes);
		return testNodes;
	}
	
	private Set<DirectTriggerDependency> getOracleDependencyNodes(){
		Map<ReqGuardGraph, DirectTriggerDependency> stepDependencyNodes = mDependenciesGraphNodes.get(mDependenciesGraphNodes.size()-1);
		Set<DirectTriggerDependency> outputNodes = new HashSet<>();
		for (DirectTriggerDependency depNode: stepDependencyNodes.values()) {
			if(! Collections.disjoint(depNode.getOutputs(), mOracleAnnotation.getOracleVars())){
				outputNodes.add(depNode);
			}
		}
		return outputNodes;
	}
	
	private Set<DirectTriggerDependency> reverseTraverseDependencyGraph(Set<DirectTriggerDependency> outputNodes) {
		Set<DirectTriggerDependency> dependencyNodes = new HashSet<>();
		Queue<DirectTriggerDependency> queue = new LinkedList<>();
		queue.addAll(outputNodes);
		while(!queue.isEmpty()) {
			DirectTriggerDependency peek = queue.poll();
			dependencyNodes.add(peek);
			for(DirectTriggerDependency determinesPeek: peek.getOutgoingNodes()) {
				//there may be loopes in the dependency graph (think a -> b, b -> a) so prevent unrolling)
				if(!queue.contains(determinesPeek) && !dependencyNodes.contains(determinesPeek)) {
					queue.add(determinesPeek);
				}
			}
		}
		return dependencyNodes; 
	}
	
	
	private String getStepsTestPlan(Set<DirectTriggerDependency> filter) {
		StringBuilder sb = new StringBuilder();
		for(int step = 0; step < mDependenciesGraphNodes.size(); step++) {
			SystemState state = mTestStates.get(step);
			int timeStep = mTestStates.get(step).getTimeStep();
			sb.append(System.getProperty("line.separator"));
			Map<ReqGuardGraph, DirectTriggerDependency> stepDependencyGraphNodes = mDependenciesGraphNodes.get(step);
			sb.append(getStepTestPlan(stepDependencyGraphNodes, state, filter, timeStep));
		}
		sb.append("------------------------------------------------------------------------------------------");
		return sb.toString();
	}

	private String getStepTestPlan(Map<ReqGuardGraph, DirectTriggerDependency> stepDependencyGraphNodes, SystemState state, Set<DirectTriggerDependency> filter, int timeStep) {
		StringBuilder sbin = new StringBuilder();
		StringBuilder sbout = new StringBuilder();
		sbin.append("Set inputs:");
		sbin.append(System.getProperty("line.separator"));
		for(ReqGuardGraph reqAut: stepDependencyGraphNodes.keySet()) {
			DirectTriggerDependency dependencyNode = stepDependencyGraphNodes.get(reqAut);
			if (!filter.contains(dependencyNode)) continue;
			//inputs
			if(dependencyNode.getInputs().size() > 0) {
				sbin.append("\t");
				sbin.append(state.getVarSetToValueSet(dependencyNode.getInputs()));
				sbin.append(System.getProperty("line.separator"));
			}
			//Outputs
			if(dependencyNode.getOutputs().size() > 0) {
				sbout.append("\t");
				sbout.append(state.getVarSetToValueSet(dependencyNode.getOutputs()));
				sbout.append("(" + dependencyNode.getReqAut().getName() + ") ");
				sbout.append(System.getProperty("line.separator"));
			}
		}
		if (sbout.length() > 0) {
			sbout.append(System.getProperty("line.separator"));
			sbin.append("Wait for at most " + Integer.toString(timeStep) + " for:" + System.getProperty("line.separator"));
			return sbin.append(sbout).toString();
		} else {
			sbin.append("Wait exactly  " + Integer.toString(timeStep));
			sbin.append(System.getProperty("line.separator"));
			return sbin.toString();
		}
		
	}
	
	
	@SuppressWarnings("unused")
	private String getStepTestPlanGraphed(Map<ReqGuardGraph, DirectTriggerDependency> stepDependencyGraphNodes, SystemState state, Set<DirectTriggerDependency> filter, double timeStep) {
		StringBuilder sbin = new StringBuilder();
		StringBuilder sbtrans = new StringBuilder();
		StringBuilder sbout = new StringBuilder();
		for(ReqGuardGraph reqAut: stepDependencyGraphNodes.keySet()) {
			DirectTriggerDependency dependencyNode = stepDependencyGraphNodes.get(reqAut);
			if (!filter.contains(dependencyNode)) continue;
			//inputs
			if(dependencyNode.getInputs().size() > 0) {
				sbin.append("Input ---------- (");
				sbin.append(state.getVarSetToValueSet(dependencyNode.getInputs()));
				sbin.append(") ----------> ");
				sbin.append(dependencyNode.getReqAut().getName());	
				sbin.append(System.getProperty("line.separator"));
			}
			//direct trigger dep.
			for(DirectTriggerDependency dependeeNode: dependencyNode.getOutgoingNodes()) {
				if (dependencyNode.getOutgoingEdgeLabel(dependeeNode).size() > 0) {
					sbtrans.append(dependeeNode.getReqAut().getName());
				} else {
					continue;
				}
				sbtrans.append("---------- (");
				sbtrans.append(state.getVarSetToValueSet((Set<TermVariable>) dependencyNode.getOutgoingEdgeLabel(dependeeNode)));
				sbtrans.append(") ----------> ");
				sbtrans.append(dependencyNode.getReqAut().getName());
				sbtrans.append(System.getProperty("line.separator"));
			}
			//Outputs
			if(dependencyNode.getOutputs().size() > 0) {
				sbout.append(dependencyNode.getReqAut().getName());
				sbout.append("---------- (");
				sbout.append(state.getVarSetToValueSet(dependencyNode.getOutputs()));
				sbout.append(") ----------> Output");	
				sbout.append(System.getProperty("line.separator"));
			}
		}
		return sbin.append(sbtrans).append(sbout).toString();
	}
	
	
	public String toString() {
		return String.format("Found Test for: %s", mOracleAnnotation.getOracleVars());
	}
	
}





















