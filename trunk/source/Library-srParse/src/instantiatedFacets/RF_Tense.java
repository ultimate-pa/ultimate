package instantiatedFacets;
import framework.ReqFacet;
import framework.Term;


public class RF_Tense {
	//Tense Facet
	private Term past = new Term ("past");
	private Term future = new Term ("future");
	private Term present = new Term ("present");
	private Term notense = new Term ("notense");
	//Term pastAndFuture = new Term ("past&Future");
	
	public ReqFacet tense;
	
	public RF_Tense(){
		this.tense = new ReqFacet("Tense", 4);	
		tense.addTerm(past);
		tense.addTerm(present);
		tense.addTerm(future);
		tense.addTerm(notense);
	}

	public Term getPast() {
		return past;
	}

	public Term getFuture() {
		return future;
	}

	public Term getPresent() {
		return present;
	}

	public Term getNotense() {
		return notense;
	}
	
}
