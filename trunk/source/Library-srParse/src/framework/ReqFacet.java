package framework;


public class ReqFacet extends Facet{
	
	//keine zusätzlichen Attribute benötigt
	
	//Constructor
	public ReqFacet(String facetname, int numberOfTerms){
		super(facetname,numberOfTerms);
		this.facetType =1; //0=kein Typ, 1=Req, 2=Log
	}
}

