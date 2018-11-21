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
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Expression2Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.AuxVarGen;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.ReqGraphAnnotation;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqGuardGraph;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqSymbolTable;

public class TestGeneratorResult implements IResult  {
	
	private final List<SystemState> mTestStates;
	private final List<List<ReqGraphAnnotation>> mStepGuards;
	private final Term mOracle;
	private final ReqGuardGraph mOracleReq;
	private final Script mScript;
	private final AuxVarGen mAuxVarGen;
	private final ReqSymbolTable mReqSymbolTable;
	private final Expression2Term mExpression2Term;
	
	public TestGeneratorResult (List<SystemState> testStates, List<List<ReqGraphAnnotation>> stepGuards, 
			ReqGraphAnnotation oracleAnnotation, Script script, ReqSymbolTable reqSymbolTable, AuxVarGen auxVarGen,
			Expression2Term expression2Term) {
		mTestStates = testStates;
		mScript = script;
		mStepGuards = stepGuards;
		mAuxVarGen = auxVarGen;
		mReqSymbolTable = reqSymbolTable;
		mOracle = SmtUtils.and(mScript, oracleAnnotation.getGuard());
		mOracleReq = oracleAnnotation.getRequirementAut();
		mExpression2Term = expression2Term;
	}

	@Override
	public String getPlugin() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getShortDescription() {
		// TODO Auto-generated method stub
		return toString();
	}

	@Override
	public String getLongDescription() {
		StringBuilder sb = new StringBuilder();
		
		sb.append("Test Vector:"+System.getProperty("line.separator"));
		
		for(int i = 0; i < mStepGuards.size(); i++) {
			//steps
			sb.append(testStepToString(i));
		}
		return sb.toString();
	}
	
	private String testStepToString(int i) {
		StringBuilder sb = new StringBuilder();
		//sb.append(mTestStates.get(i) + System.getProperty("line.separator"));			
			//labels
		sb.append("----| Step: t ");
		sb.append(Double.toString(mTestStates.get(i).getTimeStep()));
		sb.append("|-------------------------------------------------------------------------------------------");
		sb.append(System.getProperty("line.separator"));
		Map<ReqGuardGraph, ReqTriggerDependency>  dependencies = calculateStepDependencies(mStepGuards.get(i));
		for(ReqGuardGraph triggeredReqAut: dependencies.keySet()){
			ReqTriggerDependency peek = dependencies.get(triggeredReqAut);
			//TODO poject out inputs
			//sb.append(SmtUtils.getFreeVars(rgg.getGuards()).retainAll(mReqSymbolTable.getInputVars()));
			for(ReqTriggerDependency effectReqNode: peek.getOutgoingNodes()) {
				ReqGuardGraph tiggeringReqAut = effectReqNode.getReqAut();
				sb.append(tiggeringReqAut.getName());
				sb.append("(");
				Set<TermVariable> ts = SmtUtils.getFreeVars((Collection<Term>) dependencies.get(triggeredReqAut).getOutgoingEdgeLabel(effectReqNode));
				for(TermVariable v: ts) {
					sb.append(getValueOfState(i,v));
				}
				sb.append(" ) ");
			}
			Set<String> inputVarNames = mReqSymbolTable.getInputVars();
			for(TermVariable v : peek.getInputs()) {
				if(inputVarNames.contains(v.getName())) {
					sb.append(getValueOfState(i,v));
				}
			}
			sb.append(" ----> ");
			sb.append(peek.getReqAut().getName());
			sb.append(" (");
			for(TermVariable v : peek.getOutputs()) {
					sb.append(getValueOfState(i,v));
			}
			sb.append(") ");
			sb.append(System.getProperty("line.separator"));
		}
		sb.append(System.getProperty("line.separator"));
		return sb.toString();
	}
	
	
	
	private Map<ReqGuardGraph, ReqTriggerDependency> calculateStepDependencies(List<ReqGraphAnnotation> annotations) {
		//prepare nodes
		Map<ReqGuardGraph, ReqTriggerDependency> reqNodes = new HashMap<>();
		for(ReqGraphAnnotation annotation: annotations) {
			reqNodes.put(annotation.getRequirementAut(), new ReqTriggerDependency(annotation.getRequirementAut()));
		}
		//build graph
		for(ReqGraphAnnotation annotation: annotations) {
			findDependencies(annotation.getRequirementAut(), annotation.getGuard(), annotations, reqNodes);
		}
		return reqNodes;
	}	
	
	//Find the labels of reqs that set dependand's inputs
	private void findDependencies(ReqGuardGraph dependandReqAut, Term dependandTerm, 
			List<ReqGraphAnnotation> stepAnnotations, Map<ReqGuardGraph, ReqTriggerDependency> reqNodes) {
		Map<String, ReqGraphAnnotation> dependees = new HashMap<>();
		Set<TermVariable> triggerVar = new HashSet<>();
		ReqTriggerDependency dependand = reqNodes.get(dependandReqAut); 
		// get all trigger (!) variables
		for(TermVariable var: SmtUtils.getFreeVars(Arrays.asList(dependandTerm))) {
			if(! mReqSymbolTable.isAuxVar(var.toString()) && ! mAuxVarGen.getEffectVariables(dependandReqAut).contains(var)) {
				triggerVar.add(var);
			}
		}
		// find justification for trigger
		for(ReqGraphAnnotation stepAnnotation: stepAnnotations) {
			ReqGuardGraph reqId = stepAnnotation.getRequirementAut();
			Term edge = stepAnnotation.getGuard();
			Set<Term> justifiedTriggers = new HashSet<>();
			for(TermVariable effect: mAuxVarGen.getEffectVariables(reqId)) {
				if(triggerVar.contains(effect) && SmtUtils.getFreeVars(Arrays.asList(edge)).contains(effect) ) {
					triggerVar.remove(effect);
					justifiedTriggers.add(effect);
				}
			}
			if(justifiedTriggers.size() > 0) {
				ReqTriggerDependency targetDepNode = reqNodes.get(stepAnnotation.getRequirementAut());
				dependand.addOutgoingNode(targetDepNode, justifiedTriggers);
			}
			Set<TermVariable> inputs = SmtUtils.getFreeVars(Arrays.asList(edge));
			inputs.removeAll(justifiedTriggers);
			dependand.addInputs(inputs);
			Set<TermVariable> outputs = SmtUtils.getFreeVars(Arrays.asList(edge));
			outputs.retainAll(mAuxVarGen.getEffectVariables(dependandReqAut));
			dependand.addOutputs(outputs);
		}
	}
	
	private String getValueOfState(int i, TermVariable v) {
		String ident = v.getName();
		Collection<Expression> values = mTestStates.get(i).getValues(ident);
		return formatAssignment(ident, values);
	}
	
	private String formatAssignment(String ident, Collection<Expression> values) {
		StringBuilder sb = new StringBuilder();
		sb.append( ident);
		sb.append( "=" );
		for(Expression value: values) {
			sb.append( BoogiePrettyPrinter.print(value));
		}
		sb.append("; ");
		return sb.toString();
	}
	

	
	public String toString() {
		return "Fount Test for oracle: " + mTestStates.get(mTestStates.size()-1).toOracleString() ;
	}
	
}





















