package framework;



public class LogicalFacet extends Facet{
	
	//Attributes
	int termOrder[];
	
	public LogicalFacet(String facetname, int numberOfTerms){
		super (facetname, numberOfTerms);	
		this.termOrder = new int [numberOfTerms];
		for (int i=0; i<numberOfTerms; i++){
			termOrder[i]= 0;}
		//this.facetType =2; //0: Typ nicht gesetzt, 1=Req, 2=Log
	}
	
	//Methods
	public int addTerm(Term T, int order){
		if (addTerm(T)!=0){
			//case: addTerm hat funktioniert: Array hat noch Plätze frei und Term kam noch nicht vor
			int position = this.isElement(T)-1;
			this.termOrder[position]=order;
			return position+1;
		}
		else return 0;
		
	}
	

	
	
	public int deleteTerm(Term T){
		int position = super.deleteTerm(T);
		if (position !=0){
			//erfolgreich gelöscht --> war in Facette auch drin
			System.out.println("Info LogicalFacet.deleteTerm(): deletion");
			this.termOrder[position-1]=0;
			return position;
		}
		else return 0;
			}
	
	public int elementHeight(Term T){
		int position = this.isElement(T);
		if (position !=0){
			//Term ist Teil der Facette
			int height = this.termOrder[position-1];
			return height;
		}
		else //das Element ist gar nicht Teil der Facette
		{
			System.out.println("Error LogicalFacet.elementHeight(): Term "+T.Termvalue + " ist nicht Teil der Facette");
			return 0;
		}
	}
	
	public boolean smaller(Term t1, Term t2){
		
		//Prüfe: sind beide Terme Teil der Facette?
		if (this.isElement(t1)==0){
			System.out.println("Error LogicalFacet.smaller: t1= "+t1.Termvalue+" is not part of the facet");
			return false;
		}
		else 
			if (this.isElement(t2)==0){
			System.out.println("Error LogicalFacet.smaller: t2= "+t2.Termvalue+" is not part of the facet");
			return false;
			}
			else //both t1 and t2 are part of the facet
			{
				int position_t1 = this.isElement(t1)-1;
				int position_t2 = this.isElement(t2)-1;
				int termorder_t1 = this.termOrder[position_t1];
				int termorder_t2 = this.termOrder[position_t2];
				
				if (termorder_t1 < termorder_t2){
					return true;
				}
				else return false;
			}
	}
	
	public boolean top(Term t1){
		//Prüfe: ist t1 Teil der Facette?
		if (this.isElement(t1)==0){
			System.out.println("Error LogicalFacet.top: t1= "+t1.Termvalue+" is not part of the facet");
			return false;
		}
		else{
			//vergleiche t1 mit allen anderen Termen in der Facette
			for (int i =0; i<this.numberOfTerms;i++){
				Term t2 = this.termSet[i];
				if (smaller(t1,t2)){
					return false;
				}
			}
			return true;
		}
	}
	
	public boolean bottom(Term t1){
		//Prüfe: ist t1 Teil der Facette?
		if (this.isElement(t1)==0){
			System.out.println("Error LogicalFacet.bottom: t1= "+t1.Termvalue+" is not part of the facet");
			return false;
		}
		else{
			//vergleiche t1 mit allen anderen Termen in der Facette
			for (int i =0; i<this.numberOfTerms;i++){
				Term t2 = this.termSet[i];
				if (smaller(t2,t1)){
					return false;
				}
			}
			return true;
		}
	}
	
	//Wird für die Optimierung gebraucht: alle BootomElemente der Logischen Facetten erhalten den (simplicity-benefit value) Wert "2",
	//alle TopElemente erhalten den Wert 0, alle dazwischen sind "1";
	public int getWeight(Term t1){
		if (top(t1)){
			return 0;
		}
		else {
			if (bottom(t1)){
				return 2;
			}
			else return 1;
		}
	}
}


