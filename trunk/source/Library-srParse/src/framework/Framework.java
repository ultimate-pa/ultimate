package framework;


public class Framework {
	//Attributes
	ReqFacetCatalog reqFacetCatalog;
	LogFacetCatalog logFacetCatalog;
	LogAssignmentTable logAssignmentTable;
	
	//Constructor
	public Framework(ReqFacetCatalog cat1, LogFacetCatalog cat2, LogAssignmentTable tbl){
		this.reqFacetCatalog = cat1;
		this.logFacetCatalog = cat2;
		this.logAssignmentTable = tbl;
	}
	
	public ReqFacetCatalog getReqFacetCatalog() {
		return reqFacetCatalog;
	}

	public LogFacetCatalog getLogFacetCatalog() {
		return logFacetCatalog;
	}

	public LogAssignmentTable getLogAssignmentTable() {
		return logAssignmentTable;
	}
	
}
