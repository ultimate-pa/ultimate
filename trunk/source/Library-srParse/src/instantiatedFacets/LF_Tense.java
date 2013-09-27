package instantiatedFacets;
import framework.LogicalFacet;
import framework.Term;


public class LF_Tense {
	//Tense Facet
	private Term past = new Term ("past");
	private Term future = new Term ("future");
	private Term present = new Term ("present");
	private Term notense = new Term ("notense");
	private Term pastAndFuture = new Term ("past&Future");
	
	public LogicalFacet tense;
	
	public LF_Tense(){
		this.tense = new LogicalFacet("l_5",5);
		tense.addTerm(notense, 0);
		tense.addTerm(present, 0);
		tense.addTerm(future, 1);
		tense.addTerm(past, 1);
		tense.addTerm(pastAndFuture, 2);
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

	public Term getPastAndFuture() {
		return pastAndFuture;
	}
	
	
}
