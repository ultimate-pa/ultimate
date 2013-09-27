package framework;


public abstract class Facet {
	//Attributes
	String facetname;
	int numberOfTerms;
	protected Term termSet [];
	protected int i;
	private Term init;
	
	protected int facetType;
	
	//Constructors
	public Facet(String facetname, int numberOfTerms){
		this.facetname = facetname;
		this.numberOfTerms = numberOfTerms;
		this.termSet = new Term [numberOfTerms];
		this.i = 0;
		this.init = new Term ("init");
		for (int i=0; i<numberOfTerms; i++){
			termSet[i]= this.init;
		}
		this.facetType =0;
	}
	
	//Methods
	public int addTerm(Term T){
		if (i > (numberOfTerms-1)){
			System.out.println("Error addTerm: Array too small!");
			return 0;
		}
		else {
			if (this.isElement(T)==0){
				this.termSet[i] = T;
				System.out.println("Info: Term "+T.Termvalue+" was added to Facet " + this.facetname + " at position " + i);
				i++;
				return i;
			}
			else {
				System.out.println("Error addTerm: Pro Facette darf ein Term nur einmal verwendet werden");
				return 0;
			}
			
		}
	}
	
	//liefert 0 falls Term nicht in Facette enthalten, und sonst die Position des Terms im Array termSet.
	public int isElement(Term T){
		if (this.i==0){
			System.out.println("Error isElement: Facet is empty!");
			return 0;
		}
		else {
			for (int j=0; j<numberOfTerms; j++){
				if (termSet[j].Termvalue.equals(T.Termvalue)){
					//System.out.println("Info isElement(): Termset[j] an Position "+ j + " ist "+ termSet[j].Termvalue);
					return j+1;
				}
			}
			return 0;
		}
	}
	
	public int deleteTerm(Term T){
		if (this.i==0){
			System.out.println("Error deleteTerm(): Facet is empty!");
			return 0;
		}
		else {
			
			if (this.isElement(T) == 0){
				System.out.println("Error deleteTerm(): the term "+T.Termvalue+" was not in the facet and therefore could not be deleted");
				return 0;
			}
			else {
				int position = isElement(T)-1;
				termSet[position] = this.init;
				this.i--;
				return position+1;
			}
			}
		}
	
	public int getFacetType(){
		return this.facetType;
	}
	
	
	
	
	
	
	
}
