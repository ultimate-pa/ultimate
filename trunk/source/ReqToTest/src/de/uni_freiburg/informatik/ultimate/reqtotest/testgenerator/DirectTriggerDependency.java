package de.uni_freiburg.informatik.ultimate.reqtotest.testgenerator;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableLabeledEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqGuardGraph;

public class DirectTriggerDependency extends ModifiableLabeledEdgesMultigraph<DirectTriggerDependency, Set<? extends Term>> {

	private static final long serialVersionUID = 5734209642364260026L;
	
	protected ReqGuardGraph mReqAut;
	protected Set<TermVariable> mInputs = new HashSet<TermVariable>();
	protected Set<TermVariable> mOutputs = new HashSet<TermVariable>();
	
	public DirectTriggerDependency(ReqGuardGraph reqAut) {
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
	
	public void disconnect() {
		for(DirectTriggerDependency in: getIncomingNodes()) {
			in.disconnectOutgoing(this);
		}
		List<DirectTriggerDependency> remove = new ArrayList<>();
		for(DirectTriggerDependency out: getOutgoingNodes()) {
			remove.add(out);
		}
		for(DirectTriggerDependency out: remove) {
			removeOutgoingNode(out);
		}
	}

}
