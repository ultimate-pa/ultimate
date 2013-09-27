package instantiatedFacets;
import framework.ReqFacet;
import framework.Term;


public class RF_Possibility {
	//Possibility
	private Term always = new Term("always");
	private Term possible = new Term ("possible");
	private Term notense = new Term ("no tense");
	
	public ReqFacet possibility;
	
	public RF_Possibility(){
		this.possibility = new ReqFacet("possibility",3);
		possibility.addTerm(notense);
		possibility.addTerm(always);
		possibility.addTerm(possible);	
	}

	public Term getAlways() {
		return always;
	}

	public Term getPossible() {
		return possible;
	}

	public Term getNotense() {
		return notense;
	}

	public ReqFacet getPossibility() {
		return possibility;
	}
	
		
}
