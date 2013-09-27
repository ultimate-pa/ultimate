package framework;


public abstract class Assignment {
//Attribute
	FacetCatalog catalog;
	String name;
	protected int assignmentType; //soll angeben, ob Req-Assignment oder logischesAssignment (oder ganz was neues)
	protected Term[] assignment;
	private Term error = new Term("error");
	
	//Constructor
	public Assignment(FacetCatalog catalog, String name){
		this.catalog = catalog;
		this.name = name;
		this.assignment = new Term [catalog.length()];
		//this.assignmentType =0;
		
		for (int i=0; i<catalog.length();i++){
			assignment[i]=error;
		}
	}
	
	public FacetCatalog getCatalog() {
		return catalog;
	}

	public String getName() {
		return name;
	}

	//Methods
	public int assign(Term t, Facet f){
		//is the facet part of the catalog?
		int position = catalog.isElement(f);
		if (position==0){
			//the facet is not part of the catalog
			System.out.println("Error Assignment.assign: The facet is not part of the catalog");
			return 0;
		}
		else{		
			if (f.isElement(t)!=0){
				//Term ist Teil der Facette
				assignment[position-1]=t;	
				System.out.println("Info Assignment.assign(term,facet): assignment at position "+(position-1)+" is "+t.Termvalue);
				return position;
			}
			else //Term ist nicht Teil der Facette!
			{
				System.out.println("Error Assignment.assign(term,facet): the facet does not contain the term");
				return 0;
			}
		}
	}
	
	public Term getAssignment(Facet f){
		//is the facet part of the catalog?
		int position = catalog.isElement(f);
		if (position ==0){
			//the facet is not part of the catalog
			System.out.println("Error Assignment.assign: The facet is not part of the catalog");
			return error;
		}
		else //the facet is part of the catalog
		{
			return assignment[position-1];
		}
	}
	
	//public int getAssignmentType(){
		//if (this.assignmentType == 0){
			//assignmentType wurde noch nicht zugewiesen!
		//	System.out.println("Error: Assignment.getAssignmentType: AssignmentType was not set");
		//}
		//return this.assignmentType;
	//}
	
	
}
