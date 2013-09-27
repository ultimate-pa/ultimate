package framework;




public class Optimization {

	public Optimization()
	{
		;
	}
	
	public int getSimplicity(LogicalAssignment ass){
		int length = ass.getCatalog().length();
		int simplicityWeight =0;
		for(int i=0;i<length;i++){
			
			LogicalFacet f1 = (LogicalFacet) ass.getCatalog().catalog[i];
			Term assignment = ass.getAssignment(ass.getCatalog().catalog[i]);
			
			simplicityWeight = simplicityWeight + f1.getWeight(assignment);
			
		}
		return simplicityWeight;
	}
	
	public void getSimplicityAll(LogAssignmentTable table){
		int length = table.getPointerAssignmentTable();
		for (int i=0; i<length;i++){
			LogicalAssignment ass = table.table[i];
			System.out.println("The simplicity-benefitValue of "+ass.getName()+ " is " + this.getSimplicity(ass));
		}
	}
	
	public double[] getSimplicityAllArray(LogAssignmentTable table){
		int length = table.getPointerAssignmentTable();
		double [] simpl = new double[length];
		for (int i=0; i<length;i++){
			LogicalAssignment ass = table.table[i];
			int simplicity = this.getSimplicity(ass);
			simpl [i] = simplicity;
		}
		return simpl;
	}
	
	public double[] getCoverageAllArray(LogAssignmentTable table, ReqAssignmentTable tabl, TestFramework framework ){
		int length = table.getPointerAssignmentTable();
		double [] coverage = new double[length];
		for (int i=0; i<length;i++){
			LogicalAssignment ass = table.table[i];
			int covered = this.covered(tabl, ass, framework);
			coverage [i] = covered;
		}
		return coverage;
	}
	
	public int covered (ReqAssignmentTable tabl, LogicalAssignment logAss, TestFramework framework){
		int numberRows = tabl.getElementCount();//.getRemainingSlots();
		int coveredReqs = 0;
		if (numberRows==0){
			System.out.println("Error: Optimization.covered: The given ReqTable is empty!");
			return coveredReqs;
		}
		else {
			int numberColumns = tabl.table.elementAt(0).getCatalog().length();
				//Das Flag is wahr falls das Req gecovert werden kann, und false sonst
			boolean flag = true;
			for (int i=0; i < numberRows; i++) {
				flag = true;
				//Mappe zunächst jede Zeile in der ReqAssignmentTable auf ein Logisches Assignment
				LogicalAssignment mapped = framework.getMappingArray(tabl, i);
				//Prüfe dann, ob jeder Eintrag des gemappten logischen Assignment kleiner/gleich dem gegebenen ist
				//Falls ja: kann das Req gecovert werden --> erhöhe "coveredReqs"; sonst weiter
				for (int j=0; j<numberColumns; j++){
					LogicalFacet f0 = (LogicalFacet) framework.catLog.catalog[j];
					if (f0.smaller(logAss.assignment[j], mapped.assignment[j])){
					flag= false;
					}
				}
				if (flag == true){
					coveredReqs++;
				}
			}
			return coveredReqs;
			}
	}
}
