package instantiatedFacets;
import framework.ReqFacet;
import framework.Term;


public class RF_DegreeOfNecessity {
	//Attributes
	private Term error= new Term("error");
	
	private Term essential;
	private Term conditional;
	private Term optional;
	
	public ReqFacet degreeOfNecessity;
	
	//Constructor
	public RF_DegreeOfNecessity (){
		this.essential = new Term ("essential");
		this.conditional = new Term ("conditional");
		this.optional = new Term ("optional");
		
		this.degreeOfNecessity = new ReqFacet("Degree of necessity",3);
		degreeOfNecessity.addTerm(essential);
		degreeOfNecessity.addTerm(conditional);
		degreeOfNecessity.addTerm(optional);	
	}

	public Term getEssential() {
		return essential;
	}

	public Term getConditional() {
		return conditional;
	}

	public Term getOptional() {
		return optional;
	}

}
