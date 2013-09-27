package instantiatedFacets;
import framework.ReqFacet;
import framework.Term;


public class RF_ComparisonSameTS {
	//comparison facet (same timestamp)
	private Term noComparison = new Term("no comparison");
	private Term linearInequality = new Term("linear inequality");
	private Term extension = new Term("extension");
	
	public ReqFacet comparisonSameTS;
	
	public RF_ComparisonSameTS(){
		this.comparisonSameTS = new ReqFacet("comparison on same timestamps",3);
		//comparison facet (same timestamp)
		comparisonSameTS.addTerm(noComparison);
		comparisonSameTS.addTerm(linearInequality);
		comparisonSameTS.addTerm(extension);
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
