package framework;



public class LogFacetCatalog extends FacetCatalog{
	//Attributes
	private LogicalFacet init = new LogicalFacet("init",1);
	//public LogicalFacet[] catalog;

		public LogFacetCatalog(String catalogName, int numberOfFacets){
			super (catalogName, numberOfFacets);
						
			for (int i=0; i<numberOfFacets; i++){
				this.catalog[i]=init;
			}
			//this.facetType=2; //0: nicht gesetzt, 1=Reqs, 2=log
		}
		
	
}
