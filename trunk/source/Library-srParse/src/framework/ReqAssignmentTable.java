package framework;
import java.util.Vector;

public class ReqAssignmentTable {
	//Attributes
	protected int numberOfEntrys; //number of table rows
	protected Vector< ReqAssignment> table;//[] table;
	private int pointerReqAssTable; //zeigt an wie voll die Table schon ist; Annahme, Table wird nur einmalig gefüllt, es wird aber nie was gelöscht
	
	private Term error = new Term("error");
	
	//Constructor
	public ReqAssignmentTable(int numberOfEntrys){
		this.numberOfEntrys = numberOfEntrys;
		this.table = new Vector<ReqAssignment>(); //[numberOfEntrys];
		this.pointerReqAssTable =0;
	}
	
	//Constructor
	public ReqAssignmentTable(){
		this.numberOfEntrys = 0;
		this.table = new Vector<ReqAssignment>(); //[numberOfEntrys];
		this.pointerReqAssTable =0;
	}
	
	//Methods
	
	//wie voll ist Table
	public int getRemainingSlots() {
		return 1;
	}
	
	//wie viele Elemente schon drinnen
	public int getElementCount() {
		return table.size();
	}
	
	//In die Tabelle sollen nur Req-Assignments zum selben ReqAssCatalog
	public boolean fits(ReqAssignment r){
		if (pointerReqAssTable==0){
			//table leer und daher ist Typ noch egal
			return true;
		}
		else {
			if(table.elementAt(pointerReqAssTable-1).getCatalog().getCatalogName() == r.getCatalog().getCatalogName()){
				return true;
			}
			else {
				System.out.println("Error ReqAssignmentTable.fits(): The ReqAssignment does not fit to the other entrys in the table");
				return false;
			}
		}
			
	}
	
	public int addReqAssignment(ReqAssignment r){
		if (this.getRemainingSlots()==numberOfEntrys){
			//Table is full!
			System.out.println("Error: ReqAssignmentTable.addReqAssignment: table is already full");
			return 0;
		}
		else { if(this.fits(r)){
			table.add(r);
			pointerReqAssTable++;
			System.out.println("RequirementsAssignment added");
			return pointerReqAssTable;
		}
		else {
			return 0;
			}
		}	
	}
	
	public Term getReqAssignment(int row, ReqFacet facet){
		//Forderung nach Assignment in Tabelle, die noch nicht gefüllt ist
		if (row > this.getElementCount() ){
			return error;
		}
		else {
			return table.get(row).getAssignment(facet);
		}
		
	}
}
