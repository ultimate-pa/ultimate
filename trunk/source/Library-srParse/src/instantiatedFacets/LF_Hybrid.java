package instantiatedFacets;
import framework.LogicalFacet;
import framework.Term;


public class LF_Hybrid {
	//Attributes
	private Term hybrid = new Term("hybrid");
	private Term notHybrid = new Term("notHybrid");
	
	public LogicalFacet hybr;
	
	public LF_Hybrid(){
		this.hybr = new LogicalFacet("l2",2);
		hybr.addTerm(hybrid, 1);
		hybr.addTerm(notHybrid, 0);
	}

	public Term getHybrid() {
		return hybrid;
	}

	public Term getNotHybrid() {
		return notHybrid;
	}
	
	
}
