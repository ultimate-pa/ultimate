package instantiatedFacets;
import framework.ReqFacet;
import framework.Term;


public class RF_TimeConstraint {
	//Time Constraint
	private Term na = new Term("n.a.");
	private Term independent = new Term ("independent");
	private Term adjacent = new Term("adjacent");
	private Term nonadjacent = new Term("non-adjacent");
	
	public ReqFacet timeConstraint;
	
	public RF_TimeConstraint(){
		this.timeConstraint = new ReqFacet("timeConstraint",4);
		timeConstraint.addTerm(na);
		timeConstraint.addTerm(adjacent);
		timeConstraint.addTerm(nonadjacent);
		timeConstraint.addTerm(independent);
	}

	public Term getNa() {
		return na;
	}

	public Term getIndependent() {
		return independent;
	}

	public Term getAdjacent() {
		return adjacent;
	}

	public Term getNonadjacent() {
		return nonadjacent;
	}
	
	
		
}
