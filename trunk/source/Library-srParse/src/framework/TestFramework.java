package framework;
import instantiatedFacets.LF_Comparison;
import instantiatedFacets.LF_Fuzzyness;
import instantiatedFacets.LF_Hybrid;
import instantiatedFacets.LF_Quantifier;
import instantiatedFacets.LF_Relation;
import instantiatedFacets.LF_Tense;
import instantiatedFacets.LF_TimeFlow;
import instantiatedFacets.RF_ComparisonDifferentTS;
import instantiatedFacets.RF_ComparisonSameTS;
import instantiatedFacets.RF_DegreeOfNecessity;
import instantiatedFacets.RF_Possibility;
import instantiatedFacets.RF_Tense;
import instantiatedFacets.RF_TimeConstraint;
import instantiatedFacets.RF_Vagueness;
import framework.*;



public class TestFramework {
	//Attributes
	private Term error= new Term("error");
	
	//RequirementsFacetten
	public RF_DegreeOfNecessity facet1;
	public RF_Vagueness facet2;	
	public RF_ComparisonDifferentTS facet3;
	public RF_ComparisonSameTS facet4;
	public RF_Tense facet5;
	public RF_Possibility facet6;
	public RF_TimeConstraint facet7;
	
	//Logische Facetten
	public LF_Fuzzyness l_1;
	public LF_Hybrid l_2;
	public LF_Comparison l_3;
	public LF_Relation l_4;
	public LF_Tense l_5;
	public LF_TimeFlow l_6;
	public LF_Quantifier l_7;	
	
	//Facet Catalogs
	public ReqFacetCatalog catReq;
	public LogFacetCatalog catLog;
	
	//Optimierung
	public Optimization optimization;
	
	//Tabelle mit Logischen Assignments zu bekannten Logiken
	public LogAssignmentTable logicTable;
	
	
	public TestFramework(){
		//REQUIREMENTS FACETS
		this.facet1 = new RF_DegreeOfNecessity();
		this.facet2 = new RF_Vagueness();
		this.facet3 = new RF_ComparisonDifferentTS();
		this.facet4 = new RF_ComparisonSameTS();
		this.facet5 = new RF_Tense();
		this.facet6 = new RF_Possibility();
		this.facet7 = new RF_TimeConstraint();	
		
		this.catReq = new ReqFacetCatalog("catReq", 7);
		catReq.addFacet(facet1.degreeOfNecessity);
		catReq.addFacet(facet2.vagueness);
		catReq.addFacet(facet3.comparisonDifferentTS);
		catReq.addFacet(facet4.comparisonSameTS);
		catReq.addFacet(facet5.tense);
		catReq.addFacet(facet6.possibility);
		catReq.addFacet(facet7.timeConstraint);
		
		//LOGICAL FACETS
		this.l_1 = new LF_Fuzzyness();
		this.l_2 = new LF_Hybrid();
		this.l_3 = new LF_Comparison();
		this.l_4 = new LF_Relation();
		this.l_5 = new LF_Tense();
		this.l_6 = new LF_TimeFlow();
		this.l_7 = new LF_Quantifier();	
		
		this.catLog = new LogFacetCatalog("catLog",7);
		catLog.addFacet(l_1.fuzzyness);
		catLog.addFacet(l_2.hybr);
		catLog.addFacet(l_3.compar);
		catLog.addFacet(l_4.relation);
		catLog.addFacet(l_5.tense);
		catLog.addFacet(l_6.timeflow);
		catLog.addFacet(l_7.quantifier);
		
		this.optimization = new Optimization();
		
		//ASSIGNMENT ZU BEKANNTEN LOGIKEN
		this.logicTable = new LogAssignmentTable(14);
		
		//Assignment zu LTL	
		LogicalAssignment ltl = new LogicalAssignment(catLog, "LTL");		
		ltl.assign(l_1.getNotFuzzy(), l_1.fuzzyness);
		ltl.assign(l_2.getNotHybrid(), l_2.hybr);
		ltl.assign(l_3.getNoComparison(), l_3.compar);
		ltl.assign(l_4.getNoArithmetic(), l_4.relation);
		ltl.assign(l_5.getFuture(), l_5.tense);
		ltl.assign(l_6.getLinear(), l_6.timeflow);
		ltl.assign(l_7.getNa(), l_7.quantifier);
		logicTable.addLogAssignment(ltl);
		
		//Assignment zu CTL	
		this.assignLogicalTerms("CTL", l_1.getNotFuzzy(), l_2.getNotHybrid(), l_3.getNoComparison(), l_4.getNoArithmetic(), 
				l_5.getFuture(), l_6.getBranching(), l_7.getNa());
		
		//Assignment zu MTL	
		this.assignLogicalTerms("MTL", l_1.getNotFuzzy(), l_2.getNotHybrid(), l_3.getNoComparison(), l_4.getNoArithmetic(), 
				l_5.getPastAndFuture(), l_6.getLinear(), l_7.getBounded());
		
		//Assignment zu CTL_rp extended	
		this.assignLogicalTerms("CTL_rp extended", l_1.getNotFuzzy(), l_2.getHybrid(), l_3.getComparison(), l_4.getPresburger(), 
				l_5.getFuture(), l_6.getBranching(), l_7.getNa());
		
		//Assignment zu CTL*	
		this.assignLogicalTerms("CTL*", l_1.getNotFuzzy(), l_2.getNotHybrid(), l_3.getNoComparison(), l_4.getNoArithmetic(), 
				l_5.getFuture(), l_6.getLinAndBranch(), l_7.getNa());
		
		//Assignment zu TCTL
		this.assignLogicalTerms("TCTL", l_1.getNotFuzzy(), l_2.getNotHybrid(), l_3.getNoComparison(), l_4.getNoArithmetic(), 
				l_5.getFuture(), l_6.getBranching(), l_7.getBounded());
		
		//Assignment zu TCTL*
		this.assignLogicalTerms("TCTL*", l_1.getNotFuzzy(), l_2.getNotHybrid(), l_3.getNoComparison(), l_4.getNoArithmetic(), 
				l_5.getFuture(), l_6.getLinAndBranch(), l_7.getBounded());
		
		//Assignment zu XCTL
		this.assignLogicalTerms("XCTL", l_1.getNotFuzzy(), l_2.getNotHybrid(), l_3.getNoComparison(), l_4.getNoArithmetic(), 
				l_5.getFuture(), l_6.getLinear(), l_7.getClock());
		
		this.assignLogicalTerms("FLTL", l_1.getFuzzy(), l_2.getNotHybrid(), l_3.getNoComparison(), l_4.getNoArithmetic(), 
				l_5.getFuture(), l_6.getLinear(), l_7.getNa());
		
		//Assignment zu CTL* Arith	
		this.assignLogicalTerms("CTL* extended with Arith", l_1.getNotFuzzy(), l_2.getNotHybrid(), l_3.getComparison(), l_4.getExtension(), 
				l_5.getFuture(), l_6.getLinAndBranch(), l_7.getNa());
		
		//Assignment zu TCTL* Arith
		this.assignLogicalTerms("TCTL* Arith", l_1.getNotFuzzy(), l_2.getNotHybrid(), l_3.getComparison(), l_4.getExtension(), 
				l_5.getFuture(), l_6.getLinAndBranch(), l_7.getBounded());
		
		//Assignment zu boolean logic
		this.assignLogicalTerms("Boolean Logic", l_1.getNotFuzzy(), l_2.getNotHybrid(), l_3.getNoComparison(), l_4.getNoArithmetic(), 
				l_5.getNotense(), l_6.getNotense(), l_7.getNa());
		
		//Assignment zu fuzzy TCTL* with Arith & hybrid
		this.assignLogicalTerms("fuzzy TCTL* with Arith. and Hybrid", l_1.getFuzzy(), l_2.getHybrid(), l_3.getComparison(), l_4.getPresburger(), 
				l_5.getFuture(), l_6.getLinAndBranch(), l_7.getBounded());
		
		//Assignment zu "all"
		this.assignLogicalTerms("all", l_1.getFuzzy(), l_2.getHybrid(), l_3.getComparison(), l_4.getExtension(), 
				l_5.getPastAndFuture(), l_6.getLinAndBranch(), l_7.getClock());
		
		
	}
	
	//Assign the terms for all logical facets at once
	public void assignLogicalTerms(String logicName, Term fuzzy, Term hybrid, Term comparison, Term relation, Term tense, Term timeflow, Term quantifier){
		LogicalAssignment ass = new LogicalAssignment(catLog, logicName);		
		ass.assign(fuzzy , l_1.fuzzyness);
		ass.assign(hybrid, l_2.hybr);
		ass.assign(comparison, l_3.compar);
		ass.assign(relation, l_4.relation);
		ass.assign(tense, l_5.tense);
		ass.assign(timeflow, l_6.timeflow);
		ass.assign(quantifier, l_7.quantifier);
		logicTable.addLogAssignment(ass);
	}
	
	//MAPPING FUNCTIONS
	
	//Diese Funktion berechnet das logische Assignment für ALLE Einträge der 
	//Requirements-Assignments in einer ReqAssignment Table "tabl"
	public void getMapping(ReqAssignmentTable tabl){	
		System.out.println("The requirements in the table are mapped to "
		+this.mapToFuzzy(tabl).Termvalue+", "
		+this.mapToHybrid(tabl).Termvalue+", "
		+this.mapToComparison(tabl).Termvalue+", "
		+this.mapToArithmetic(tabl).Termvalue+", "
		+this.mapToTempOperator(tabl).Termvalue+", "
		+this.mapToTimeFlow(tabl).Termvalue+", "
		+this.mapToTimeConstraint(tabl).Termvalue		
		);	
	}
	
	
	//Diese Funktion mapt ein Requirements Assignment aus der Zeile "row" der ReqAssignment Table "tabl"
	// auf ein logisches Assignment
	public LogicalAssignment getMappingArray(ReqAssignmentTable tabl, int row){	
		LogicalAssignment ass = new LogicalAssignment(this.catLog, tabl.table.elementAt(row).name);
		ass.assign(this.mapTermToFuzzy(row, tabl), this.l_1.fuzzyness);
		ass.assign(this.mapTermToHybrid(row, tabl), this.l_2.hybr);
		ass.assign(this.mapTermToComparison(row, tabl), this.l_3.compar);
		ass.assign(this.mapTermToArithmetic(row, tabl), this.l_4.relation);
		ass.assign(this.mapTermToTempOperator(row, tabl), this.l_5.tense);
		ass.assign(this.mapTermToTimeFlow(row, tabl), this.l_6.timeflow);
		ass.assign(this.mapTermToTimeConstraint(row, tabl), this.l_7.quantifier);		
		return ass;	
	}
	
	
	//////////////////////////FACETTE VAGUENESS ---> LOG FACETTE FUZZYNESS
	//MappingFunction Reqfacets: Rank // Vagueness --> LogFacet: Fuzzyness
	public Term mapTermToFuzzy(int row, ReqAssignmentTable tabl){
		if (row > tabl.getElementCount()){
			//The assignment table has no assignment at the asked for entry
			System.out.println("Error TestFramework.mapToFuzzy: The ReqAssignmentTable has no assignment at row "+row);
			return error;
		}
		else {
			Term rank = tabl.getReqAssignment(row, facet1.degreeOfNecessity);
			Term vague = tabl.getReqAssignment(row, facet2.getVagueness());
			if((rank.Termvalue != "essential")|| (vague.Termvalue == "vague")){
				return l_1.getFuzzy();
			}
			else return l_1.getNotFuzzy();
		}
		
	}
	
	public Term mapToFuzzy(ReqAssignmentTable tabl){				
		for (int i =0; i<tabl.getElementCount();i++){
			if (this.mapTermToFuzzy(i, tabl).Termvalue== l_1.getFuzzy().Termvalue){
				System.out.println("Info TestFramework.mapToFuzzy: A term was mapped to fuzzy");
				return l_1.getFuzzy();
			}
		}
		return l_1.getNotFuzzy();		
	}
	
	//////////////////////////FACETTE COMPARISON ---> LOG FACETTE HYBRID
	//MappingFunction Reqfacets: comparison between timestamps --> LogFacet: Hybrid
	public Term mapTermToHybrid(int row, ReqAssignmentTable tabl){
		if (row > tabl.getElementCount()){
			//The assignment table has no assignment at the asked for entry
			System.out.println("Error TestFramework.mapToHybrid: The ReqAssignmentTable has no assignment at row "+row);
			return error;
		}
		else {
			Term diff_ts = tabl.getReqAssignment(row, facet3.comparisonDifferentTS);
			if(diff_ts.Termvalue != facet3.getNoComparison().Termvalue){
				return l_2.getHybrid();
			}
			else return l_2.getNotHybrid();
		}
		
	}
	
	public LogAssignmentTable getLogicTable() {
		return logicTable;
	}
	
	public String[] getLogicNames(){
		int length = this.logicTable.numberOfEntrys;
		String[] arr = new String[length];
		for (int i=0; i< length; i++){
			LogicalAssignment ass = this.getLogicTable().table[i];
			String name = ass.getName();
			arr[i] = name;
		}
		return arr;
	}

	public Term mapToHybrid(ReqAssignmentTable tabl){				
		for (int i =0; i<tabl.getElementCount();i++){
			if (this.mapTermToHybrid(i, tabl).Termvalue== l_2.getHybrid().Termvalue){
				System.out.println("Info TestFramework.mapToHybrid: A term was mapped to hybrid");
				return l_2.getHybrid();
			}
		}
		return l_2.getNotHybrid();		
	}
	
	//////////////////////////FACETTE COMPARISON ---> LOG FACETTE COMPARISON
	//mapt pro Reihe der Req-Assignment Tabelle auf ein logisches Assignment
	//MappingFunction Reqfacets: comparison between timestamps & comparison same timestamp --> LogFacet: comparison
	public Term mapTermToComparison(int row, ReqAssignmentTable tabl){
		if (row > tabl.getElementCount()){
			//The assignment table has no assignment at the asked for entry
			System.out.println("Error TestFramework.mapToComparison: The ReqAssignmentTable has no assignment at row "+row);
			return error;
		}
		else {
			Term diff_ts = tabl.getReqAssignment(row, facet3.comparisonDifferentTS);
			Term same_ts = tabl.getReqAssignment(row, facet4.comparisonSameTS);
			if(diff_ts.Termvalue != facet3.getNoComparison().Termvalue ||
					same_ts.Termvalue != facet4.getNoComparison().Termvalue){
				return l_3.getComparison();
			}
			else return l_3.getNoComparison();
		}
		
	}
	//geht alle Reihen des ReqAssignments durch und mapt dann auf l_3
	public Term mapToComparison(ReqAssignmentTable tabl){				
		for (int i =0; i<tabl.getElementCount();i++){
			if (this.mapTermToComparison(i, tabl).Termvalue== l_3.getComparison().Termvalue){
				//System.out.println("Info TestFramework.mapToComparison: A term was mapped to comparison");
				return l_3.getComparison();
			}
		}
		return l_3.getNoComparison();		
	}
	
//////////////////////////FACETTE COMPARISON ---> LOG FACETTE ARITHMETIC
	//mapt pro Reihe der Req-Assignment Tabelle auf ein logisches Assignment
	//MappingFunction Reqfacets: comparison between timestamps & comparison same timestamp --> LogFacet: Arithmetic
	//Wichtig: funktioniert so nur wegen Auswertungsreihenfolge!
	public Term mapTermToArithmetic(int row, ReqAssignmentTable tabl){
		if (row > tabl.getElementCount()){
			//The assignment table has no assignment at the asked for entry
			System.out.println("Error TestFramework.mapToArithmetic: The ReqAssignmentTable has no assignment at row "+row);
			return error;
		}
		else {
			Term diff_ts = tabl.getReqAssignment(row, facet3.comparisonDifferentTS);
			Term same_ts = tabl.getReqAssignment(row, facet4.comparisonSameTS);
			if(diff_ts.Termvalue == facet3.getExtension().Termvalue ||
					same_ts.Termvalue == facet4.getExtension().Termvalue){
				return l_4.getExtension();
			}
			else {
				if (diff_ts.Termvalue == facet3.getLinearInequality().Termvalue ||
						same_ts.Termvalue == facet4.getLinearInequality().Termvalue){
					return l_4.getPresburger();
				}
				else return l_4.getNoArithmetic();
			}
		}
		
	}
	
	//geht alle Reihen des ReqAssignments durch und mapt dann auf l_3
	public Term mapToArithmetic(ReqAssignmentTable tabl){		
		//speichert das bisher "größte" assignment der tabelle; Am Anfang der Suche ist das "nOArithmetic"=Bottomelement
		Term highestassignment = l_4.getNoArithmetic();
		for (int i =0; i<tabl.getElementCount();i++){			
			if (this.mapTermToArithmetic(i, tabl).Termvalue== l_4.getExtension().Termvalue){
				//System.out.println("Info TestFramework.mapToComparison: A term was mapped to extension");
				//da extension das Top-Element ist kann man hier auch die Suche abbrechen - etwas höheres findet man eh nicht
				return l_4.getExtension();
			}
			else {
				if (this.mapTermToArithmetic(i, tabl).Termvalue == l_4.getPresburger().Termvalue){
					highestassignment = l_4.getPresburger();
				}
			}
		}
		return highestassignment;		
	}
	
	
	//////////////////////////FACETTE TENSE ---> LOG FACETTE TENSE OPERATOR
	//mapt pro Reihe der Req-Assignment Tabelle auf ein logisches Assignment
	//MappingFunction Reqfacets: tense --> LogFacet: temp operator
	public Term mapTermToTempOperator(int row, ReqAssignmentTable tabl){
		if (row > tabl.getElementCount()){
			//The assignment table has no assignment at the asked for entry
			System.out.println("Error TestFramework.mapToTempOperator: The ReqAssignmentTable has no assignment at row "+row);
			return error;
		}
		else {
			Term tense = tabl.getReqAssignment(row, facet5.tense);
			if(tense.Termvalue == facet5.getFuture().Termvalue){
				return l_5.getFuture();
			}
			else {
				if(tense.Termvalue == facet5.getPast().Termvalue){
					return l_5.getPast();
				}
				else return l_5.getNotense();
			}
		}
		
	}
	//geht alle Reihen des ReqAssignments durch und mapt dann auf l_5
	public Term mapToTempOperator(ReqAssignmentTable tabl){	
		//in der Variable merken wir uns das bisher höchste Assignment
		Term highestAssignment = l_5.getNotense();
		for (int i =0; i<tabl.getElementCount();i++){
			if ((this.mapTermToTempOperator(i, tabl).Termvalue== l_5.getFuture().Termvalue && highestAssignment==l_5.getPast()) ||
					(this.mapTermToTempOperator(i, tabl).Termvalue == l_5.getPast().Termvalue && highestAssignment==l_5.getFuture())){
				return l_5.getPastAndFuture(); //jetzt haben wir das Topelement erreicht und können Suche abbrechen
												// den Fall future/past & pastUndFuture müssen wir nicht betrachten, da wir bei einem pastUndFuture nicht mehr in der schleife wären
			}
			else {//case 2: Fall "future" und highestAssignment ist etwas anderes als Past (--> niedriger)
				if (this.mapTermToTempOperator(i, tabl).Termvalue== l_5.getFuture().Termvalue){
					highestAssignment = l_5.getFuture();
				}
				else {
					if (this.mapTermToTempOperator(i, tabl).Termvalue == l_5.getPast().Termvalue){
						highestAssignment = l_5.getPast();
					}
				}
			}
		}
		return highestAssignment;		
	}
	
	//////////////////////////FACETTE POSSIBILITY ---> LOG FACETTE TIME FLOW
	//mapt pro Reihe der Req-Assignment Tabelle auf ein logisches Assignment
	//MappingFunction Reqfacets: possibility --> LogFacet: time flow
	public Term mapTermToTimeFlow(int row, ReqAssignmentTable tabl){
		if (row > tabl.getElementCount()){
			//The assignment table has no assignment at the asked for entry
			System.out.println("Error TestFramework.mapToTimeFlow: The ReqAssignmentTable has no assignment at row "+row);
			return error;
		}
		else {
			Term tense = tabl.getReqAssignment(row, facet6.possibility);
			if(tense.Termvalue == facet6.getPossible().Termvalue){
				return l_6.getBranching();
			}
			else {
				if(tense.Termvalue == facet6.getAlways().Termvalue){
					return l_6.getLinear();
				}
				else return l_6.getNotense();
			}
		}
	}
	
	//geht alle Reihen des ReqAssignments durch und mapt dann auf l_6
	public Term mapToTimeFlow(ReqAssignmentTable tabl){	
		//in der Variable merken wir uns das bisher höchste Assignment
		Term highestAssignment = l_6.getNotense();
		for (int i =0; i<tabl.getElementCount();i++){
			if ((this.mapTermToTimeFlow(i, tabl).Termvalue== l_6.getBranching().Termvalue && highestAssignment==l_6.getLinear()) ||
					(this.mapTermToTimeFlow(i, tabl).Termvalue == l_6.getLinear().Termvalue && highestAssignment==l_6.getBranching())){
				return l_6.getLinAndBranch(); //jetzt haben wir das Topelement erreicht und können Suche abbrechen
												// den Fall future/past & pastUndFuture müssen wir nicht betrachten, da wir bei einem pastUndFuture nicht mehr in der schleife wären
			}
			else {//case 2: Fall "future" und highestAssignment ist etwas anderes als Past (--> niedriger)
				if (this.mapTermToTimeFlow(i, tabl).Termvalue== l_6.getBranching().Termvalue){
					highestAssignment = l_6.getBranching();
				}
				else {
					if (this.mapTermToTimeFlow(i, tabl).Termvalue == l_6.getLinear().Termvalue){
						highestAssignment = l_6.getLinear();
					}
				}
			}
		}
		return highestAssignment;		
	}
	
	
//////////////////////////FACETTE TIME CONSTRAINT ---> LOG FACETTE QUANTIFIER
	//mapt pro Reihe der Req-Assignment Tabelle auf ein logisches Assignment
	//MappingFunction Reqfacets: time constraint --> LogFacet: time quantifier
	public Term mapTermToTimeConstraint(int row, ReqAssignmentTable tabl){
		if (row > tabl.getElementCount()){
			//The assignment table has no assignment at the asked for entry
			System.out.println("Error TestFramework.mapToTimeConstraint: The ReqAssignmentTable has no assignment at row "+row);
			return error;
		}
		else {
			Term tense = tabl.getReqAssignment(row, facet7.timeConstraint);
			if(tense.Termvalue == facet7.getIndependent().Termvalue){
				return l_7.getClock();
			}
			else {
				if(tense.Termvalue == facet7.getNonadjacent().Termvalue){
					return l_7.getFreezed();
				}
				else 
					if(tense.Termvalue == facet7.getAdjacent().Termvalue){
					return l_7.getBounded();
				}
					else return l_7.getNa();
			}
		}
	}
	
	//geht alle Reihen des ReqAssignments durch und mapt dann auf l_6
	public Term mapToTimeConstraint(ReqAssignmentTable tabl){	
		//in der Variable merken wir uns das bisher höchste Assignment
		Term highestAssignment = l_7.getNa();
		for (int i =0; i<tabl.getElementCount();i++){
			Term mappedTerm = this.mapTermToTimeConstraint(i, tabl);
			if (l_7.quantifier.smaller(highestAssignment,mappedTerm)){
				highestAssignment=mappedTerm;
			}	
		}
		return highestAssignment;		
	}
	
	


	//BEGINN DES TESTS
	public static void main(String args []) {
			
		TestFramework testrun = new TestFramework();
		ReqAssignmentTable ReqTbl = new ReqAssignmentTable(2);
		
		ReqAssignment r1 = new ReqAssignment(testrun.catReq, "r1");
		ReqAssignment r2 = new ReqAssignment(testrun.catReq, "r2");
		
		
		
		
		//Assignment von A_Req
		//r1 ist (essential, not vague, no comp, no comp, future, always, n.a)
		r1.assign(testrun.facet1.getEssential(), testrun.facet1.degreeOfNecessity);
		r1.assign(testrun.facet2.getNotVague(), testrun.facet2.vagueness);
		r1.assign(testrun.facet3.getNoComparison(), testrun.facet3.comparisonDifferentTS);
		r1.assign(testrun.facet4.getNoComparison(), testrun.facet4.comparisonSameTS);
		r1.assign(testrun.facet5.getFuture(), testrun.facet5.tense);
		r1.assign(testrun.facet6.getAlways(), testrun.facet6.possibility);
		r1.assign(testrun.facet7.getNa(), testrun.facet7.timeConstraint);
		//r2 ist (essential, not vague, lin inequ, no comp, past, always, indep)
		r2.assign(testrun.facet1.getEssential(), testrun.facet1.degreeOfNecessity);
		System.out.println("The assignment of r2 is "+r2.getAssignment(testrun.facet1.degreeOfNecessity).Termvalue);
		r2.assign(testrun.facet2.getNotVague(), testrun.facet2.vagueness);
		r2.assign(testrun.facet3.getLinearInequality(), testrun.facet3.comparisonDifferentTS);
		r2.assign(testrun.facet4.getNoComparison(), testrun.facet4.comparisonSameTS);
		r2.assign(testrun.facet5.getPast(), testrun.facet5.tense);
		r2.assign(testrun.facet6.getAlways(), testrun.facet6.possibility);
		r2.assign(testrun.facet7.getIndependent(), testrun.facet7.timeConstraint);
		//r1.assign(vague, vagueness);
				
		//tenseLogical.smaller(adjacent, notense);
		//System.out.println("The term t1 is smaller than t2: "+tenseLogical.smaller(future, notense));
		//System.out.println("The term t1 is smaller than t2: "+tenseLogical.smaller(future, pastAndFuture));
		
		System.out.println("Info: ReqAssignment table added new ReqAssignment at position "+(ReqTbl.addReqAssignment(r1)-1));
		System.out.println("Info: try fits "+r2.getName()+ " to ReqAssignmentTable :"+ReqTbl.fits(r2));
		System.out.println("Info: ReqAssignment table added new ReqAssignment at position "+(ReqTbl.addReqAssignment(r2)-1));
						
		//System.out.println("Mapping to fuzzy : "+ testrun.mapToFuzzy(ReqTbl).Termvalue);
		//System.out.println("Mapping to hybrid : "+ testrun.mapToHybrid(ReqTbl).Termvalue);
		//System.out.println("Mapping to comparison : "+ testrun.mapToComparison(ReqTbl).Termvalue);
		//System.out.println("Mapping to arithmetic : "+ testrun.mapToArithmetic(ReqTbl).Termvalue);
		//System.out.println("Mapping to temporal operator : "+ testrun.mapToTempOperator(ReqTbl).Termvalue);
		//System.out.println("Mapping to time flow : "+ testrun.mapToTimeFlow(ReqTbl).Termvalue);
		//System.out.println("Mapping to time constraint : "+ testrun.mapToTimeConstraint(ReqTbl).Termvalue);
		testrun.getMapping(ReqTbl);
		
		//System.out.println("Top of time constraint : "+ testrun.l_7.quantifier.getWeight(testrun.l_7.getBounded()));
		//System.out.println("Optimierung: Simplicity : "+ testrun.optimization.getSimplicity(testrun.logicTable.table[0]));
		testrun.optimization.getSimplicityAll(testrun.logicTable);
		testrun.getMappingArray(ReqTbl, 0);
		
		System.out.println("The logic "+ testrun.logicTable.table[0].name + " covers "+ testrun.optimization.covered(ReqTbl, testrun.logicTable.table[0], testrun)+" requirements out of "+ReqTbl.getElementCount());
		System.out.println("The logic "+ testrun.logicTable.table[13].name + " covers "+ testrun.optimization.covered(ReqTbl, testrun.logicTable.table[13], testrun)+" requirements out of "+ReqTbl.getElementCount());
		
	}
}
