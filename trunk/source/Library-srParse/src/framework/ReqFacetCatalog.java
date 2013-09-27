package framework;


public class ReqFacetCatalog extends FacetCatalog{
	
	//Attributes
	private ReqFacet init = new ReqFacet("init",1);

		public ReqFacetCatalog(String catalogName, int numberOfFacets){
			super (catalogName, numberOfFacets);
			
			for (int i=0; i<numberOfFacets; i++){
				this.catalog[i]=init;
			}
			//this.facetType=1; //0: nicht gesetzt, 1=Reqs, 2=log
		}
}
