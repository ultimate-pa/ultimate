package pea;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.Vector;

import pea.modelchecking.TCSWriter;

public class VacuousAssignment extends TCSWriter{
	
	/**
     * FileWriter to output file.
     */
    protected BufferedWriter writer; 
    protected boolean rename;
    protected PhaseEventAutomata pea2write;
    private int i=0;
    
    private Vector<CDD> possiblyVacuous; //list of formulas such that the pea this formula was generated from, 
    //gets vacuously satisfied if this formula holds in every state of the parallel product
    private Vector<CDD> possibleVacuousMaker; //list of formulas, such that the pea this formulas was generated from, cannot be vacuously satisfied 
    private Vector<String> vacuousReqNames;

	//however it might lead to a vacuous satisfaction for other peas
    private Vector<CDD> vacuous; //list of the formulae that are really vacuously satisfied
   
    
    public VacuousAssignment(String fileName, PhaseEventAutomata pea) {
        super(fileName);
        this.pea2write = pea;
        this.possiblyVacuous = new Vector<CDD>();
        this.setVacuous(new Vector<CDD>());
        this.setPossibleVacuousMaker(new Vector<CDD>());
        this.setVacuousReqNames(new Vector<String>());
    }

    /**
     * Constructor setting output file name and rename flag that indicates
     * whether original location names have to be used or whether the locations
     * are renamed into default names.
     * 
     * @param file
     * @param rename
     */
   
	public VacuousAssignment(String destfile, boolean rename, PhaseEventAutomata pea) {
		this(destfile, pea);
        this.rename = rename;
        this.possiblyVacuous = new Vector<CDD>();
        this.setVacuous(new Vector<CDD>());
        this.setPossibleVacuousMaker(new Vector<CDD>());
        this.setVacuousReqNames(new Vector<String>());
	}

	public void getVacuousAssignments(PhaseEventAutomata pea) throws IOException{
		System.out.println("*********************************************************");
		System.out.println("Queries to check for a vacuous satisfaction for PEA "+pea.getName());
		Phase[] init = pea.getInit();
		int numberOfLocations = pea.getPhases().length;
		if (numberOfLocations <0) {
			System.out.println("ERROR: The pea is empty");
		}
		if (numberOfLocations ==1){
			CDD cdd = pea.getPhases()[0].getStateInvariant();

			int length = this.getPossibleVacuousMakerLength();
			for (int i=0; i<length; i++){
				CDD poss = this.getPossibleVacuousMaker().elementAt(i);
				if (cdd.implies(poss)){
					this.addToVacuous(cdd);
				}
				else if (poss.implies(cdd)){
					this.addToVacuous(poss);	
				}
			}
			this.addToPossVacuousMaker(cdd);

			String vacString = cdd.toString("uppaal", true);	        			
			System.out.println("A[]("+vacString+");");
			this.writer.write("A[]("+vacString+");");
			this.writer.newLine();
			this.writer.flush();

		}
		else{
			int numberOfInitStates = init.length;
			for (int i=0; i<numberOfInitStates; i++){
				Phase initState = init[i];
				//States that have a clockinvariant !=0 have to be left when the clock is expired
				//Thus such states cannot lead to a vacuous satisfaction
				if (initState.getClockInvariant() == CDD.TRUE){
					CDD vac = initState.getStateInvariant();
					this.addToPossiblyVacuous(vac);

					String vacString = vac.toString("uppaal", true);	        			
					System.out.println("A[]("+vacString+");");
					this.writer.write("A[]("+vacString+");");
					this.writer.newLine();
					this.writer.flush();
				}

			}
			System.out.println("*********************************************************");
		}

	}
	 
	 public void getVacuousAssignments(PhaseEventAutomata pea, String reqName) throws IOException{
		 
		 this.getVacuousAssignments(pea);
//	    	System.out.println("*********************************************************");
//	    	System.out.println("Queries to check for a vacuous satisfaction for PEA "+pea.getName());
//	    	Phase[] init = pea.getInit();
//	    	int numberOfLocations = pea.getPhases().length;
//	    	if (numberOfLocations <0) {
//	    		System.out.println("ERROR: The pea is empty");
//	    	}
//	    	if (numberOfLocations ==1){
//	    		CDD cdd = pea.getPhases()[0].getStateInvariant();
//	    		
//	    		if (this.getPossibleVacuousMaker().isEmpty()){
//	    			this.addToPossVacuousMaker(cdd);
//	    		}
//	    		else {
//	    			int length = this.getPossibleVacuousMakerLength();
//	    			for (int i=0; i<length; i++){
//		    			CDD poss = this.getPossibleVacuousMaker().elementAt(i);
//		    			if (cdd.implies(poss)){
//		    				this.addToVacuous(cdd);
//		    				this.addToPossVacuousMaker(cdd);
//		    			}
//		    			else if (poss.implies(cdd)){
//		    				this.addToVacuous(poss);
//		    				this.addToPossVacuousMaker(cdd);
//		    			}
//		    			else this.addToPossVacuousMaker(cdd);
//		    			
//		    		}	    			
//	    		}
//	    		this.writer.write("PEA "+pea.getName()+" has only 1 state");
//    			this.writer.write("A[]("+cdd.toString("uppaal", true)+");");
//    			this.writer.newLine();
//    			this.writer.flush();
//	    		
//	    		
////	    		if (cdd.isAtomic()) {
////	    			this.writer.write("This requirement can only be satisfied non-vacuously. "+"\n");
////	    			this.possibleVacuousMaker.add(cdd);
////		    		this.writer.newLine();
////		    		System.out.println("PEA "+pea.getName()+" has only 1 state with an atomic proposition thus it cannot become vacuously satisfied");
////	    		}
////	    		else {
////	    			this.possiblyVacuous.add(cdd);
////	    		}
//	    	}
//	    	else{
//	    		int numberOfInitStates = init.length;
//	        	for (int i=0; i<numberOfInitStates; i++){
//	        		Phase initState = init[i];
//	        		//States that have a clockinvariant !=0 have to be left when the clock is expired
//	        		//Thus such states cannot lead to a vacuous satisfaction
//	        		if (initState.getClockInvariant() == CDD.TRUE){
//	        			CDD vac = initState.getStateInvariant();
//	        			this.addToPossiblyVacuous(vac);
//	        			
//	        			String vacString = vac.toString("uppaal", true);	        			
//	        			System.out.println("A[]("+vacString+");");
//	        			this.writer.write("A[]("+vacString+");");
//	        			this.writer.newLine();
//	        			this.writer.flush();
//	        		}
//	        		
//	        	}
//	        	System.out.println("*********************************************************");
//	    	}
	    	
	    }
	 
	 //INPUT: PEA as parallel product of the requirements you want to check for vacuous satisfaction
	 //Precondition: you built up the parallel product and in doing so built-up the vector "vacuous" as well
	 public void checkVacuousSatisfiability(PhaseEventAutomata pea){
		 Vector<CDD> vac = this.getPossiblyVacuous();
		 
		 if (vac.isEmpty()){
			 System.out.println("Before checking for vacuous satisfaction, you need to built-up the vacuous-vector");
		 }
		 else
			 {
			 checkPossiblyVacuous(pea);	 
			 checkPossibleVacuousMaker(pea);
			 }
	 }
	 
	 private void checkPossiblyVacuous(PhaseEventAutomata pea){
		 Phase[] phases = pea.getPhases();  
		 Vector<CDD> vac = this.getPossiblyVacuous();
		 
		 if (phases.length>1){
			 for (int j=0; j<vac.size(); j++){
				 Boolean testVacuous = true;
				 CDD formula = vac.elementAt(j);
				 
				 for (int q=0; q<phases.length; q++){
					 Phase a = phases[q];
					 CDD state = a.getStateInvariant();
					 if (state.and(formula) == CDD.FALSE){
						 testVacuous = false;
					 }
				 }
				 if (testVacuous == true){
					 this.addToVacuous(formula);
				 }
			 }
		 }		
	 }
	 
	 private void checkPossibleVacuousMaker(PhaseEventAutomata pea){
		 Vector<CDD> possMaker = this.getPossibleVacuousMaker();
		 Vector<CDD> vacCandidate = this.getPossiblyVacuous();
		 
		 if (possMaker.isEmpty()||vacCandidate.isEmpty()){
			 System.out.println("no possible vacuous formulas known OR no possible vacuous maker known");
		 }
		 else
			 
		 {	
			 Boolean testVacuous = false;
			 for (int j=0; j<possMaker.size() && !testVacuous; j++){
				 
				 CDD formula = possMaker.elementAt(j);
				 
				 for (int q=0; q<vacCandidate.size(); q++){
					 CDD state = vacCandidate.elementAt(q);
					 if (formula.implies(state)){
						 testVacuous = true;
						 this.addToVacuous(state);
						 this.addToVacuous(formula);
					 }
				 }
		}}
			 
	 }
	 
	 public void startWriting(){
		 try {
	            //this.writer = new FileWriter(fileName);
	            this.writer = new BufferedWriter(new FileWriter(fileName));

	            this.writer
	            .write("Preamble:\n"
	                        + " Queries to check for a vacuous satisfaction for PEA"); 
	            this.writer.newLine();
	            
	            this.writer.flush();
	           
	        } catch (IOException e) {
	            throw new RuntimeException(e);
	        }
			
	 }
	 
	 public void stopWriting() throws IOException{
		 this.writer.close();
		System.out.println("Successfully written to "+fileName);
			
	 }

	@Override
	public void write() {
		try {
            this.writer = new BufferedWriter(new FileWriter("fileName"));            
            //init();
            this.getVacuousAssignments(pea2write);         
            this.writer.flush();
            this.writer.close();
            System.out.println("Successfully written to "+fileName);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
		
	}
	
	public void writePEA(PhaseEventAutomata pea) {
		try {
			this.writer.write("Queries to check for requirement "+i);
			this.writer.newLine();
			i++;
            this.getVacuousAssignments(pea);  
            this.writer.newLine();
            this.writer.flush();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
		
	}
	
	

	@Override
	protected void writeAndDelimiter(Writer writer) throws IOException {
		// TODO Auto-generated method stub
		
	}

	@Override
	protected void writeDecision(Decision decision, int child, Writer writer)
			throws IOException {
		// TODO Auto-generated method stub
		
	}

	

	public Vector<CDD> getPossiblyVacuous() {
		return possiblyVacuous;
	}
	
	

	public void setVacuous(Vector<CDD> vacuous) {
		this.vacuous = vacuous;
	}

	public Vector<CDD> getVacuous() {
		return vacuous;
	}
	
	public void addToVacuous(CDD cdd) {
		if (this.vacuous.contains(cdd)){
			return;
		}
		else
		this.vacuous.add(cdd);
	}
	
	public void addToPossiblyVacuous(CDD cdd) {
		if (this.possiblyVacuous.contains(cdd)){
			return;
		}
		else
		this.possiblyVacuous.add(cdd);
	}
	
	public void addToPossVacuousMaker(CDD cdd) {
		if (this.possibleVacuousMaker.contains(cdd)){
			return;
		}
		else
		this.possibleVacuousMaker.add(cdd);
	}
	
	public void addToVacuousReqNames(String name) {
		if (this.vacuousReqNames.contains(name)){
			return;
		}
		else
		this.vacuousReqNames.add(name);
	}
	
	public Vector<CDD> getPossibleVacuousMaker() {
			return possibleVacuousMaker;
		}
	
	private int getPossibleVacuousMakerLength() {
		return possibleVacuousMaker.size();
	}

	private void setPossibleVacuousMaker(Vector<CDD> possibleVacuousMaker) {
		this.possibleVacuousMaker = possibleVacuousMaker;
		}
	
	public Vector<String> getVacuousReqNames() {
		return vacuousReqNames;
	}

	private void setVacuousReqNames(Vector<String> vacuousReqNames) {
		this.vacuousReqNames = vacuousReqNames;
	}

	
}
