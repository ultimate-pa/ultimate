package framework;


public abstract class FacetCatalog {

	//Attributes
	String catalogName;
	int numberOfFacets;	
	Facet[] catalog;
	private int countFacets;
	
	protected int facetType;
	
	
	//Constructors
	public FacetCatalog(String catalogName, int numberOfFacets){
		this.catalogName = catalogName;
		this.numberOfFacets = numberOfFacets;
		this.catalog = new Facet[numberOfFacets];
		this.countFacets =0;
		//this.facetType =0;
		}
	
	//Methods
	public int addFacet(Facet f){
		if (countFacets < numberOfFacets){
			//Catalog has still place for more facets
			//&& this.facetType==f.getFacetType()
			if (this.isElement(f)==0 ){ //Catalog is empty 
				catalog[countFacets]=f;
				countFacets++;
				return countFacets;
			}
			else //Facettenname schon vergeben!
			{
				System.out.println("Error FacetCatalog.addFacet(): The Catalog already contains a facet with the same name! Names must be unique OR the facetType does not match");
				return 0;
			}
		}
		else {
			//Catalog is full!
			System.out.println("Error FacetCatalog.addFacet: Catalog is full");
			return 0;
		}
	}
	
	public String getCatalogName() {
		return catalogName;
	}

	public Facet[] getCatalog() {
		return catalog;
	}

	public int length(){
		return numberOfFacets;
	}
	
	public int isElement(Facet f){
		if (countFacets==0){
			//Catalog is empty
			System.out.println("Error FacetCatalog.isElement(): The Catalog is empty");
			return 0;
		}
		else {
			for (int i=0; i<catalog.length;i++){
				if (catalog[i].facetname.equals(f.facetname)){
					return i+1;
				}
			}
			return 0;
		}
	}
}
