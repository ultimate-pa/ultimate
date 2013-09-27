package instantiatedFacets;
import framework.ReqFacet;
import framework.Term;


public class RF_ComparisonDifferentTS {

	//comparison facet (different timestamps)
	private Term noComparison = new Term("no comparison");
	private Term linearInequality = new Term("linear inequality");
	private Term extension = new Term("extension");
	
	public ReqFacet comparisonDifferentTS;
	
	public RF_ComparisonDifferentTS(){
		this.comparisonDifferentTS = new ReqFacet("comparison on different timestamps",3);
		comparisonDifferentTS.addTerm(noComparison);
		comparisonDifferentTS.addTerm(linearInequality);
		comparisonDifferentTS.addTerm(extension);
	}
	
	public Term getNoComparison() {
		return noComparison;
	}

	public Term getLinearInequality() {
		return linearInequality;
	}

	public Term getExtension() {
		return extension;
	}
	
}
