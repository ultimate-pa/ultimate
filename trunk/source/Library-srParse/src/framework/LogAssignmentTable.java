package framework;


public class LogAssignmentTable {
	//Attributes
	//protected int facetType; //catalogType: ReqFacetCatalog or LogFacetCatalog
	protected int numberOfEntrys; //number of table rows
	protected LogicalAssignment[] table;
	private int pointerAssignmentTable; //zeigt an wie voll die Table schon ist; Annahme, Table wird nur einmalig gefüllt, es wird aber nie was gelöscht
	
	
	//Constructor
	public LogAssignmentTable(int numberOfEntrys){
		//this.facetType=2; //Req=1; Log=2
		this.numberOfEntrys = numberOfEntrys;
		this.table = new LogicalAssignment[numberOfEntrys];
		this.pointerAssignmentTable =0;
	}
	
	public int getPointerAssignmentTable() {
		return pointerAssignmentTable;
	}
	
	public int addLogAssignment(LogicalAssignment ass){
		if (pointerAssignmentTable < numberOfEntrys){
			//still place for new assignments in the table && right type
			table[pointerAssignmentTable]=ass;
			pointerAssignmentTable++;
			return pointerAssignmentTable;
		}
		else //table is already full OR typemismatch
		{
			System.out.println("Error: LogAssignmentTable.addLogAssignment: table is already full");
				return 0;
			
		}
	}
	
	
	
	
}
