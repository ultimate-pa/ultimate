package de.uni_freiburg.informatik.ultimate.reqtotest.testgenerator;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableLabeledEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqGuardGraph;

public class ReqTriggerDependency extends ModifiableLabeledEdgesMultigraph<ReqTriggerDependency, Set<? extends Term>> {

	private static final long serialVersionUID = 5734209642364260026L;
	
	private ReqGuardGraph mReqAut;
	private Set<TermVariable> mInputs = new HashSet<TermVariable>();
	private Set<TermVariable> mOutputs = new HashSet<TermVariable>();
	
	public ReqTriggerDependency(ReqGuardGraph reqAut) {
		mReqAut = reqAut;
	}
	
	public ReqGuardGraph getReqAut() {
		return mReqAut;
	}
	
	public void addInputs(Set<TermVariable> variables) {
		mInputs.addAll(variables);
	}
	
	public Set<TermVariable> getInputs(){
		return mInputs;
	}
	
	public void addOutputs(Set<TermVariable> variables) {
		mOutputs.addAll(variables);
	}
	
	public Set<TermVariable> getOutputs(){
		return mOutputs;
	}

}
