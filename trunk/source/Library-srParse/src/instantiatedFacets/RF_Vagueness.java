package instantiatedFacets;
import framework.ReqFacet;
import framework.Term;


public class RF_Vagueness {
	
	private Term vague;
	private Term notVague;
	public ReqFacet vagueness;
	
	

	//Constructor
	public RF_Vagueness(){
		//Vagueness
		this.vague = new Term("vague");
		this.notVague = new Term("notVague");
		this.vagueness = new ReqFacet("Vagueness",2);		
		vagueness.addTerm(vague);
		vagueness.addTerm(notVague);
	}
	
	public ReqFacet getVagueness() {
		return vagueness;
	}

	public Term getVague() {
		return vague;
	}

	public Term getNotVague() {
		return notVague;
	}
	
	
	
	
}
