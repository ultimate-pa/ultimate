package de.uni_freiburg.informatik.ultimate.reqtotest.testgenerator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
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
	
	public TestGeneratorResult (List<SystemState> testStates, List<List<ReqGraphAnnotation>> stepGuards, 
			ReqGraphAnnotation oracleAnnotation, Script script, ReqSymbolTable reqSymbolTable, AuxVarGen auxVarGen) {
		mTestStates = testStates;
		mScript = script;
		mStepGuards = stepGuards;
		mAuxVarGen = auxVarGen;
		mReqSymbolTable = reqSymbolTable;
		mOracle = SmtUtils.and(mScript, oracleAnnotation.getGuards());
		mOracleReq = oracleAnnotation.getRequirementIds().get(0); //TODO: This should be ok..
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
		
		
		for(int i = 0; i < mStepGuards.size(); i++) {
			Map<ReqGuardGraph, Set<ReqGuardGraph>> dep = calculateTreeStep(mStepGuards.get(i));
			for(ReqGuardGraph rgg: dep.keySet()){
				sb.append(rgg.getName());
				sb.append(" -depends on->> ");
				for(ReqGuardGraph rgd: dep.get(rgg)) {
					sb.append(rgd.getName());
					sb.append(",");
				}
				sb.append(";   ");
			}
			sb.append("\n");
		}
		
		
		sb.append("Test Vector:"+System.getProperty("line.separator"));
		for(ProgramState<Expression> s : mTestStates) {
			sb.append(s.toString() + System.getProperty("line.separator"));
		}
		return sb.toString();
	}
	
	
	private Map<ReqGuardGraph, Set<ReqGuardGraph>> calculateTreeStep(List<ReqGraphAnnotation> edges) {
		Map<ReqGuardGraph, Set<ReqGuardGraph>> dependency = new HashMap<>();
		for(ReqGraphAnnotation edge: edges) {
			Set<ReqGuardGraph> dependees = findDependencies(edge.getRequirementIds().get(0), 
					edge.getGuards().get(0), edges);
			dependency.put(edge.getRequirementIds().get(0), dependees);
		}
		return dependency;
	}
	
	//Find the labels of reqs that set dependands inputs
	private Set<ReqGuardGraph> findDependencies(ReqGuardGraph dependandReqId, Term dependand, List<ReqGraphAnnotation> stepAnnotations) {
		Set<ReqGuardGraph> dependees = new HashSet<>();
		Set<TermVariable> toFind = new HashSet<>();
		for(TermVariable var: SmtUtils.getFreeVars(Arrays.asList(dependand))) {
			if(! mReqSymbolTable.isAuxVar(var.toString()) && ! mAuxVarGen.getEffectVariables(dependandReqId).contains(var)) {
				toFind.add(var);
			}
		}
		for(ReqGraphAnnotation annot: stepAnnotations) {
			ReqGuardGraph reqId = annot.getRequirementIds().get(0);
			Term edge = annot.getGuards().get(0);
			for(TermVariable effect: mAuxVarGen.getEffectVariables(reqId)) {
				if(toFind.contains(effect) && SmtUtils.getFreeVars(Arrays.asList(edge)).contains(effect) ) {
					toFind.remove(effect);
					dependees.add(reqId);
				}
			}
		}
		return dependees;
	}
	
	public String toString() {
		return "Fount Test for oracle: " + mTestStates.get(mTestStates.size()-1).toOracleString() ;
	}
	
}





















