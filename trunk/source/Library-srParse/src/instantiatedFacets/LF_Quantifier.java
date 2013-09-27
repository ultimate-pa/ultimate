package instantiatedFacets;
import framework.LogicalFacet;
import framework.Term;


public class LF_Quantifier {
	//Attributes
	private Term na = new Term ("n.a.");
	private Term bounded = new Term ("bounded");
	private Term freezed = new Term ("freezed");
	private Term clock = new Term ("clock");
	
	public LogicalFacet quantifier;
	
	public LF_Quantifier(){
		this.quantifier = new LogicalFacet("l7", 4);
		quantifier.addTerm(na, 0);
		quantifier.addTerm(bounded, 1);
		quantifier.addTerm(freezed, 2);
		quantifier.addTerm(clock, 3);
	}

	public Term getNa() {
		return na;
	}

	public Term getBounded() {
		return bounded;
	}

	public Term getFreezed() {
		return freezed;
	}

	public Term getClock() {
		return clock;
	}
	
	
}
