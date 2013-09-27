package framework;



public class ReqAssignment extends Assignment{
	//keine zusätzlichen Attribute benötigt
	
	//constructor
	public ReqAssignment(ReqFacetCatalog catalog, String name){
		super(catalog,name);
		//this.assignmentType = 1; //1 entspricht dem Req Assignment; 2 dem logischen Assignment
	}
}
