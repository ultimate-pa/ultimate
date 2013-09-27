package instantiatedFacets;
import framework.LogicalFacet;
import framework.Term;


public class LF_Relation {
	//Attributes
	private Term noArithmetic = new Term ("noArithmetic");
	private Term Presburger = new Term("PresburgerArithmetic");
	private Term extension = new Term ("extension");
	
	public LogicalFacet relation;
	
	public LF_Relation(){
		this.relation= new LogicalFacet ("l4", 3);
		relation.addTerm(noArithmetic, 0);
		relation.addTerm(Presburger, 1);
		relation.addTerm(extension, 2);
	}

	public Term getNoArithmetic() {
		return noArithmetic;
	}

	public Term getPresburger() {
		return Presburger;
	}

	public Term getExtension() {
		return extension;
	}
	
	
}
