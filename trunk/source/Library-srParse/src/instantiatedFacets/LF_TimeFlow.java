package instantiatedFacets;
import framework.LogicalFacet;
import framework.Term;


public class LF_TimeFlow {
	//Attributes 
	private Term notense = new Term ("notense");
	private Term linear = new Term ("linear");
	private Term branching = new Term ("branching");
	private Term linAndBranch = new Term ("linear and branching");
	
	public LogicalFacet timeflow;
	
	public LF_TimeFlow(){
		this.timeflow = new LogicalFacet("l6",4);
		timeflow.addTerm(notense, 0);
		timeflow.addTerm(linear, 1);
		timeflow.addTerm(branching, 1);
		timeflow.addTerm(linAndBranch, 2);
	}

	public Term getNotense() {
		return notense;
	}

	public Term getLinear() {
		return linear;
	}

	public Term getBranching() {
		return branching;
	}

	public Term getLinAndBranch() {
		return linAndBranch;
	}
	
	

}
