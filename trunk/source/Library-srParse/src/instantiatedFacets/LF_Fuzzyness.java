package instantiatedFacets;
import framework.LogicalFacet;
import framework.Term;


public class LF_Fuzzyness {
	//Fuzzyness
	private Term fuzzy = new Term ("fuzzy");
	private Term notFuzzy = new Term ("notFuzzy");	
	
	public LogicalFacet fuzzyness;
	
	public LF_Fuzzyness(){
		this.fuzzyness = new LogicalFacet("l1",2);
		fuzzyness.addTerm(fuzzy,1);
		fuzzyness.addTerm(notFuzzy, 0);
	}
	
	public Term getFuzzy() {
		return fuzzy;
	}

	public Term getNotFuzzy() {
		return notFuzzy;
	}
	
	
}
