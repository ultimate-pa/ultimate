package de.uni_freiburg.informatik.ultimate.reqtotest.testgenerator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Term;
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
			mLogger.warn(String.format("connecting intra-step dependency %s for source locations %d", toJustifyAnnotation.getRequirementAut().getName(), 
					toJustifyAnnotation.getSourceLocation().getLabel()));
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
				mLogger.warn(String.format("connecting dependency %s, %s, %s", toJustifyAnnotation.getRequirementAut().getName(), 
						justifications.toString(), annotation.getRequirementAut().getName()));
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

		sb.append(getStepTestPlan());
		return sb.toString();
	}
	
	private String getStepTestPlan() {
		StringBuilder sb = new StringBuilder();
		for(Map<ReqGuardGraph, DirectTriggerDependency> stepDependencyGraphNodes: mDependenciesGraphNodes) {
			sb.append("----| Step: t ");
			//TODO time (sb.append(Double.toString(mTestStates.get(i).getTimeStep()));)
			sb.append("|-------------------------------------------------------------------------------------------");
			sb.append(System.getProperty("line.separator"));
			for(ReqGuardGraph reqAut: stepDependencyGraphNodes.keySet()) {
				DirectTriggerDependency dependencyNode = stepDependencyGraphNodes.get(reqAut);
				for(DirectTriggerDependency dependeeNode: dependencyNode.getOutgoingNodes()) {
					sb.append(dependeeNode.getReqAut().getName());
					sb.append("----------");
					sb.append(dependencyNode.getOutgoingEdgeLabel(dependeeNode).toString());
					sb.append("---------->");
					sb.append(dependencyNode.getReqAut().getName());
					sb.append(System.getProperty("line.separator"));
				}
				if(dependencyNode.getInputs().size() > 0 || dependencyNode.getOutputs().size() > 0) {
					sb.append(dependencyNode.getInputs().toString());
					sb.append("----------(");
					sb.append(dependencyNode.getReqAut().getName());
					sb.append(")---------->");
					sb.append(dependencyNode.getOutputs().toString());	
					sb.append(System.getProperty("line.separator"));
				}
			}
		}
		return sb.toString();
	}
	
	public String toString() {
		return "Fount Test for oracle: " + mTestStates.get(mTestStates.size()-1).toOracleString() ;
	}
	
}





















