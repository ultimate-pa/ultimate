package de.uni_freiburg.informatik.ultimate.lib.pea;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.Vector;

import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.TCSWriter;

public class VacuousAssignment extends TCSWriter {
	/**
	 * FileWriter to output file.
	 */
	protected BufferedWriter writer;
	protected boolean rename;
	protected PhaseEventAutomata pea2write;
	private int i = 0;
	
	private final Vector<CDD> possiblyVacuous; //list of formulas such that the pea this formula was generated from,
	//gets vacuously satisfied if this formula holds in every state of the parallel product
	private Vector<CDD> possibleVacuousMaker; //list of formulas, such that the pea this formulas was generated from, cannot be vacuously satisfied
	private Vector<String> vacuousReqNames;
	
	//however it might lead to a vacuous satisfaction for other peas
	private Vector<CDD> vacuous; //list of the formulae that are really vacuously satisfied
	
	public VacuousAssignment(final String fileName, final PhaseEventAutomata pea) {
		super(fileName);
		pea2write = pea;
		possiblyVacuous = new Vector<>();
		setVacuous(new Vector<CDD>());
		setPossibleVacuousMaker(new Vector<CDD>());
		setVacuousReqNames(new Vector<String>());
	}
	
	/**
	 * Constructor setting output file name and rename flag that indicates
	 * whether original location names have to be used or whether the locations
	 * are renamed into default names.
	 * 
	 * @param file
	 * @param rename
	 */
	
	public VacuousAssignment(final String destfile, final boolean rename, final PhaseEventAutomata pea) {
		this(destfile, pea);
		this.rename = rename;
		setVacuous(new Vector<CDD>());
		setPossibleVacuousMaker(new Vector<CDD>());
		setVacuousReqNames(new Vector<String>());
	}
	
	public void getVacuousAssignments(final PhaseEventAutomata pea) throws IOException {
		System.out.println("*********************************************************");
		System.out.println("Queries to check for a vacuous satisfaction for PEA " + pea.getName());
		final Phase[] init = pea.getInit();
		final int numberOfLocations = pea.getPhases().length;
		if (numberOfLocations < 0) {
			System.out.println("ERROR: The pea is empty");
		}
		if (numberOfLocations == 1) {
			final CDD cdd = pea.getPhases()[0].getStateInvariant();
			
			final int length = getPossibleVacuousMakerLength();
			for (int i = 0; i < length; i++) {
				final CDD poss = getPossibleVacuousMaker().elementAt(i);
				if (cdd.implies(poss)) {
					addToVacuous(cdd);
				} else if (poss.implies(cdd)) {
					addToVacuous(poss);
				}
			}
			addToPossVacuousMaker(cdd);
			
			final String vacString = cdd.toString("uppaal", true);
			System.out.println("A[](" + vacString + ");");
			writer.write("A[](" + vacString + ");");
			writer.newLine();
			writer.flush();
			
		} else {
			final int numberOfInitStates = init.length;
			for (int i = 0; i < numberOfInitStates; i++) {
				final Phase initState = init[i];
				//States that have a clockinvariant !=0 have to be left when the clock is expired
				//Thus such states cannot lead to a vacuous satisfaction
				if (initState.getClockInvariant() == CDD.TRUE) {
					final CDD vac = initState.getStateInvariant();
					addToPossiblyVacuous(vac);
					
					final String vacString = vac.toString("uppaal", true);
					System.out.println("A[](" + vacString + ");");
					writer.write("A[](" + vacString + ");");
					writer.newLine();
					writer.flush();
				}
				
			}
			System.out.println("*********************************************************");
		}
		
	}
	
	public void getVacuousAssignments(final PhaseEventAutomata pea, final String reqName) throws IOException {
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
	public void checkVacuousSatisfiability(final PhaseEventAutomata pea) {
		final Vector<CDD> vac = getPossiblyVacuous();
		
		if (vac.isEmpty()) {
			System.out.println("Before checking for vacuous satisfaction, you need to built-up the vacuous-vector");
		} else {
			checkPossiblyVacuous(pea);
			checkPossibleVacuousMaker(pea);
		}
	}
	
	private void checkPossiblyVacuous(final PhaseEventAutomata pea) {
		final Phase[] phases = pea.getPhases();
		final Vector<CDD> vac = getPossiblyVacuous();
		
		if (phases.length > 1) {
			for (int j = 0; j < vac.size(); j++) {
				boolean testVacuous = true;
				final CDD formula = vac.elementAt(j);
				
				for (int q = 0; q < phases.length; q++) {
					final Phase a = phases[q];
					final CDD state = a.getStateInvariant();
					if (state.and(formula) == CDD.FALSE) {
						testVacuous = false;
					}
				}
				if (testVacuous) {
					addToVacuous(formula);
				}
			}
		}
	}
	
	private void checkPossibleVacuousMaker(final PhaseEventAutomata pea) {
		final Vector<CDD> possMaker = getPossibleVacuousMaker();
		final Vector<CDD> vacCandidate = getPossiblyVacuous();
		
		if (possMaker.isEmpty() || vacCandidate.isEmpty()) {
			System.out.println("no possible vacuous formulas known OR no possible vacuous maker known");
		} else {
			boolean testVacuous = false;
			for (int j = 0; j < possMaker.size() && !testVacuous; j++) {
				final CDD formula = possMaker.elementAt(j);
				
				for (int q = 0; q < vacCandidate.size(); q++) {
					final CDD state = vacCandidate.elementAt(q);
					if (formula.implies(state)) {
						testVacuous = true;
						addToVacuous(state);
						addToVacuous(formula);
					}
				}
			}
		}
		
	}
	
	public void startWriting() {
		try {
			//this.writer = new FileWriter(fileName);
			writer = new BufferedWriter(new FileWriter(fileName));
			
			writer.write("Preamble:\n Queries to check for a vacuous satisfaction for PEA");
			writer.newLine();
			
			writer.flush();
			
		} catch (final IOException e) {
			throw new RuntimeException(e);
		}
		
	}
	
	public void stopWriting() throws IOException {
		writer.close();
		System.out.println("Successfully written to " + fileName);
	}
	
	@Override
	public void write() {
		try {
			writer = new BufferedWriter(new FileWriter("fileName"));
			//init();
			this.getVacuousAssignments(pea2write);
			writer.flush();
			writer.close();
			System.out.println("Successfully written to " + fileName);
		} catch (final IOException e) {
			throw new RuntimeException(e);
		}
	}
	
	public void writePEA(final PhaseEventAutomata pea) {
		try {
			writer.write("Queries to check for requirement " + i);
			writer.newLine();
			i++;
			this.getVacuousAssignments(pea);
			writer.newLine();
			writer.flush();
		} catch (final IOException e) {
			throw new RuntimeException(e);
		}
	}
	
	@Override
	protected void writeAndDelimiter(final Writer writer) throws IOException {
		// TODO Auto-generated method stub
	}
	
	@Override
	protected void writeDecision(final Decision decision, final int child, final Writer writer)
			throws IOException {
		// TODO Auto-generated method stub
	}
	
	public Vector<CDD> getPossiblyVacuous() {
		return possiblyVacuous;
	}
	
	public void setVacuous(final Vector<CDD> vacuous) {
		this.vacuous = vacuous;
	}
	
	public Vector<CDD> getVacuous() {
		return vacuous;
	}
	
	public void addToVacuous(final CDD cdd) {
		if (vacuous.contains(cdd)) {
			return;
		}
		vacuous.add(cdd);
	}
	
	public void addToPossiblyVacuous(final CDD cdd) {
		if (possiblyVacuous.contains(cdd)) {
			return;
		}
		possiblyVacuous.add(cdd);
	}
	
	public void addToPossVacuousMaker(final CDD cdd) {
		if (possibleVacuousMaker.contains(cdd)) {
			return;
		}
		possibleVacuousMaker.add(cdd);
	}
	
	public void addToVacuousReqNames(final String name) {
		if (vacuousReqNames.contains(name)) {
			return;
		}
		vacuousReqNames.add(name);
	}
	
	public Vector<CDD> getPossibleVacuousMaker() {
		return possibleVacuousMaker;
	}
	
	private int getPossibleVacuousMakerLength() {
		return possibleVacuousMaker.size();
	}
	
	private void setPossibleVacuousMaker(final Vector<CDD> possibleVacuousMaker) {
		this.possibleVacuousMaker = possibleVacuousMaker;
	}
	
	public Vector<String> getVacuousReqNames() {
		return vacuousReqNames;
	}
	
	private void setVacuousReqNames(final Vector<String> vacuousReqNames) {
		this.vacuousReqNames = vacuousReqNames;
	}
}
