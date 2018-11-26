package de.uni_freiburg.informatik.ultimate.reqtotest.testgenerator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.AuxVarGen;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.ReqGraphAnnotation;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqGuardGraph;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqSymbolTable;

public class TestGeneratorResult implements IResult  {
	
	private final List<SystemState> mTestStates;
	private final List<List<ReqGraphAnnotation>> mStepsAnnotations;
	private final List<Map<ReqGuardGraph, DirectTriggerDependency>> mDependenciesGraphNodes = new ArrayList<>();
	private final AuxVarGen mAuxVarGen;
	private final ReqSymbolTable mReqSymbolTable;
	private final ILogger mLogger;
	
	public TestGeneratorResult (ILogger logger, List<SystemState> testStates, List<List<ReqGraphAnnotation>> stepsAnnotations, 
			ReqGraphAnnotation oracleAnnotation, ReqSymbolTable reqSymbolTable, AuxVarGen auxVarGen) {
		mTestStates = testStates;
		mStepsAnnotations = stepsAnnotations;
		mAuxVarGen = auxVarGen;
		mReqSymbolTable = reqSymbolTable;
		mLogger = logger;
		calculateDependencyGraph();	
		trimTestPlan();
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
	 * Calculate relations between Requiremens in one test step.
	 * A relation looks like req1 ---- var1,var2 ----> req2, read as req2's trigger vars depend on effects var1, var2 set by req1.
	 */
	private Map<ReqGuardGraph, DirectTriggerDependency> calculateDependencyGraphStep(List<ReqGraphAnnotation> stepAnnotations, 
			Map<ReqGuardGraph, DirectTriggerDependency> lastStepDependencies) {
		//generate Nodes for every requirement 
		Map<ReqGuardGraph, DirectTriggerDependency> stepDependencyNodes = new HashMap<>();
		for(ReqGraphAnnotation annotation: stepAnnotations) {
			ReqGuardGraph reqAut = annotation.getRequirementAut();
			DirectTriggerDependency dependencyNode = new DirectTriggerDependency(reqAut);
			stepDependencyNodes.put(reqAut, dependencyNode);
		}
		//find dependees justifying every annotation
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
			if(annotation == toJustifyAnnotation) {
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
		Set<TermVariable> varsToJustify = SmtUtils.getFreeVars( Arrays.asList(toJustifyAnnotation.getGuard()) );
		Set<String> inputVariables = mReqSymbolTable.getOutputVars();
		Set<TermVariable> outputs = new HashSet<TermVariable>();
		for(TermVariable var: varsToJustify) {
			if(inputVariables.contains(var.getName())) {
				outputs.add(var);
			}
		}
		dependencyNode.addOutputs(outputs);	
	}
	
	
	private void trimTestPlan() {
		for(int step = mDependenciesGraphNodes.size()-1; step >= 0 ; step--) {
			mLogger.warn("Pruing  ..." + Integer.toString(step));
			Set<ReqGuardGraph> keepNodes = new HashSet<>();
			Map<ReqGuardGraph, DirectTriggerDependency> stepDependencyGraphNodes = mDependenciesGraphNodes.get(step);
			for(ReqGuardGraph reqAut: stepDependencyGraphNodes.keySet()) {
				DirectTriggerDependency depNode = stepDependencyGraphNodes.get(reqAut);
				mLogger.warn("Calc ..." + Integer.toString(step));
				mLogger.warn("Outdegreee              ..." + Integer.toString(depNode.getIncomingNodes().size()));
				if(depNode.getIncomingNodes().size() > 0 && depNode.getOutputs().size() > 0) {
					for(DirectTriggerDependency targetNode: depNode.getOutgoingNodes()) {
						mLogger.warn("Disconnecting ..." + targetNode.getReqAut().getName());
					}
					keepNodes.add(reqAut);
				}
			}
			stepDependencyGraphNodes.keySet().removeAll(keepNodes);
		}
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

		sb.append(getStepsTestPlan());
		return sb.toString();
	}
	
	private Set<TermVariable> getOracleTermVars(){
		Set<TermVariable> oracleVars = new HashSet<>();
		Map<ReqGuardGraph, DirectTriggerDependency> stepDependencyGraphNodes = mDependenciesGraphNodes.get(mDependenciesGraphNodes.size()-1);
		for(ReqGuardGraph reqAut: stepDependencyGraphNodes.keySet()) {
			DirectTriggerDependency dependencyNode = stepDependencyGraphNodes.get(reqAut);
			if(dependencyNode.getOutputs().size() > 0) {
				oracleVars.addAll(dependencyNode.getOutputs());
			}
		}
		return oracleVars;
	}
	
	private String getStepsTestPlan() {
		StringBuilder sb = new StringBuilder();
		for(int step = 0; step < mDependenciesGraphNodes.size(); step++) {
			SystemState state = mTestStates.get(step);
			sb.append("----| Step: t ");
			sb.append(Double.toString(mTestStates.get(step).getTimeStep()));
			sb.append("|-------------------------------------------------------------------------------------------");
			sb.append(System.getProperty("line.separator"));
			Map<ReqGuardGraph, DirectTriggerDependency> stepDependencyGraphNodes = mDependenciesGraphNodes.get(step);
			sb.append(getStepTestPlan(stepDependencyGraphNodes, state));
		}
		return sb.toString();
	}

	
	private String getStepTestPlan(Map<ReqGuardGraph, DirectTriggerDependency> stepDependencyGraphNodes, SystemState state) {
		StringBuilder sbin = new StringBuilder();
		StringBuilder sbtrans = new StringBuilder();
		StringBuilder sbout = new StringBuilder();
		for(ReqGuardGraph reqAut: stepDependencyGraphNodes.keySet()) {
			DirectTriggerDependency dependencyNode = stepDependencyGraphNodes.get(reqAut);
			mLogger.warn(dependencyNode.getIncomingNodes());
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
		return String.format("Found Test for: %s", getOracleTermVars());
	}
	
}





















