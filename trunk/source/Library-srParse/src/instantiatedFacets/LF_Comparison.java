package instantiatedFacets;
import framework.LogicalFacet;
import framework.Term;


public class LF_Comparison {
	//Attributes
	private Term noComparison = new Term ("noComparison");
	private Term comparison = new Term ("comparison");
	
	public LogicalFacet compar;
	
	public LF_Comparison(){
		this.compar= new LogicalFacet("l3",2);
		compar.addTerm(noComparison, 0);
		compar.addTerm(comparison, 1);
	}

	public Term getNoComparison() {
		return noComparison;
	}

	public Term getComparison() {
		return comparison;
	}
	
	
}
