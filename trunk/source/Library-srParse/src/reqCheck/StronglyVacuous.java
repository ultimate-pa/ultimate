package reqCheck;
/*
 **
 * The class <code>StronglyVacuous</code> builds up for a given requirements set R the parallelProductAutomaton A_R 
 * and checks for every requirement r whether r is only vacuosly satisfied in R
 * 
 * Precondition: We assume that every requirement is given as a requirement that is no parallelproduct in itself
 * Thus, for patterns like the invariance-pattern we need to transform the statenames beforehand!
 * 
 * @author Amalinda Oertel
 * April 2010
 * 
 * @see J2UPPAALWriter
 */

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.List;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import PatternLanguage.PL_initiatedPattern;
import PatternLanguage.RequirementsSet;



//import PatternLanguage.PL_Pattern2Logic;

import pea.CDD;
import pea.Phase;
import pea.PhaseEventAutomata;
import pea.Transition;
import pea.VacuousAssignment;
import pea.modelchecking.DOTWriter;
import pea.modelchecking.J2UPPAALConverter;
import pea.reqCheck.PEAPhaseIndexMap;
import pea.reqCheck.PatternToPEA;

public class StronglyVacuous {
	
	int maxIndex;
	Vector vacuous= new Vector();;	
	PhaseEventAutomata parallel;
	
	DOTWriter dotwriter = new DOTWriter("C:/test/vacuous.dot");
	
	/** Get CPU time in nanoseconds. */
	public long getCpuTime( ) {		
	    ThreadMXBean bean = ManagementFactory.getThreadMXBean( );
	    return bean.isCurrentThreadCpuTimeSupported( ) ?
	        bean.getCurrentThreadCpuTime( ) : 0L;
	}
	
	public void getVacuousProc1(RequirementsSet reqSet){		 
		 
		 int reqSetSize = reqSet.getReqSetSize();
		 int[] lastStatesPerComponent = new int[reqSetSize];
		 int[] lastStatesInParallelProduct;
		 //PhaseEventAutomata parallel;
		 		 
		 if (reqSetSize <1) {
			 System.out.println("ERROR: There is no requirement in the requirements set");
		 }
		 else		
		 {
			// vacuous = new Vector();
			 //build up an array with the maximal index per component(component==requirement)
			 // and build up parallel automaton 
			 	Vector<PhaseEventAutomata> reqSetAsPEA= reqSet.transformToPEA();
			 	PhaseEventAutomata pea;
			 	int lastState;
			 	pea = reqSetAsPEA.elementAt(0);
				lastState = this.getHighestIndex(pea);
				this.addLastStatesForComp(lastStatesPerComponent, 0, lastState);
			 	parallel = pea;
				 for (int i=1; i< reqSet.getReqSetSize();i++){
					 pea = reqSetAsPEA.elementAt(i);
					 
					 String dest = "C:/test/vacuous_single"+i+".dot";
					 dotwriter.write(dest, pea);
					 dest = "C:/test/vacuous_parallel"+i+".dot";
					 dotwriter.write(dest, parallel);
					 
					 lastState = this.getHighestIndex(pea);
					 this.addLastStatesForComp(lastStatesPerComponent, i, lastState);
					 parallel = parallel.parallel(pea);
					 if (parallel.isEmpty()){
						 reqSet.setInconsistent(true);
						 System.out.println("The requirements set is inconsistent");
						 return;
					 }
					 System.out.println("current nr of states of A_R: "+parallel.getPhases().length);
				 }
				 
				 //Then get maximal index of the parallel automaton
				 lastStatesInParallelProduct = this.getMaxIndexOfParallelProd(parallel);
				 //Then compare the indices
				 this.compare(lastStatesPerComponent, lastStatesInParallelProduct, reqSet);
				 
				 J2UPPAALConverter converter = new J2UPPAALConverter();
				 converter.writePEA2UppaalFile("C:/vacuous/testPSSVeto.xml", parallel);
		 }
		 
	}
	
	public void getVacuous2(RequirementsSet reqSet, String dest){
		 Vector<PL_initiatedPattern> reqs = reqSet.getRequirementsSetInitPattern();
		 this.getVacuousProc2(reqs, dest);
	}
	
	public void getVacuous2(Vector<PL_initiatedPattern> reqs, String dest){
		 this.getVacuousProc2(reqs, dest);
	}
	
	public void getVacuous(Vector<Integer> maxIndexPerComp, PhaseEventAutomata parallel){
		if (parallel.isEmpty()){
			 System.out.println("The requirements set is inconsistent");
			 return;
		 }
		if (maxIndexPerComp.size()==0){
			System.out.println("The vector maxIndexPerComp is empty!");
			return;
		}
		this.parallel = parallel;
		int[] lastStatesPerComponent = new int[maxIndexPerComp.size()];
		for (int i =0; i<maxIndexPerComp.size();i++){
			lastStatesPerComponent[i] = maxIndexPerComp.elementAt(i);
		}
		//Nimm an dass parallel ebenso viele komponenten besitzt wie maxIndexPerComp
		//Then get maximal index of the parallel automaton
		 int[]lastStatesInParallelProduct = this.getMaxIndexOfParallelProd(parallel);
		 //Then compare the indices
		 this.compare(lastStatesPerComponent, lastStatesInParallelProduct);
		 System.out.println("Current number of states: "+parallel.getNumberOfLocations());
	}
	
	public void getVacuousProc2(Vector<PL_initiatedPattern> reqs, String dest){		 
		 
		 int reqSetSize = reqs.size();
		 int[] lastStatesPerComponent = new int[reqSetSize];
		 int[] lastStatesInParallelProduct;
		 //PhaseEventAutomata parallel;
		 		 
		 if (reqSetSize <1) {
			 System.out.println("ERROR: There is no requirement in the requirements set");
		 }
		 else		
		 {
			// vacuous = new Vector();
			 //build up an array with the maximal index per component(component==requirement)
			 // and build up parallel automaton 
			 PatternToPEA peaTrans=new PatternToPEA();
			 	
			 	PhaseEventAutomata pea;
			 	int lastState;
			 	pea = reqs.elementAt(0).transformToPEA();
				lastState = this.getHighestIndex(pea);
				this.addLastStatesForComp(lastStatesPerComponent, 0, lastState);
			 	parallel = pea;
				 for (int i=1; i< reqSetSize;i++){
					 
					 
					 pea = reqs.elementAt(i).transformToPEA();
					 
					 //dotwriter.write(dest+"_"+i+".dot", pea);
					 //dotwriter.write(dest+"_p"+i+".dot", parallel);
					 
					 lastState = this.getHighestIndex(pea);
					 this.addLastStatesForComp(lastStatesPerComponent, i, lastState);
					 parallel = parallel.parallel(pea);
					 if (parallel.isEmpty()){
						 System.out.println("The requirements set is inconsistent");
						 return;
					 }
					 System.out.println("Step: "+i+": current nr of states of A_R: "+parallel.getPhases().length);
					 
					//Then get maximal index of the parallel automaton
					 lastStatesInParallelProduct = this.getMaxIndexOfParallelProd(parallel);
					 //Then compare the indices
					 this.compare(lastStatesPerComponent, lastStatesInParallelProduct);
				 }
				 
				 WeakVacuous weakVac = new WeakVacuous();
				 weakVac.checkInvariants(reqs, parallel);
				 
				 //Then get maximal index of the parallel automaton
				 //lastStatesInParallelProduct = this.getMaxIndexOfParallelProd(parallel);
				 //Then compare the indices
				 //this.compare(lastStatesPerComponent, lastStatesInParallelProduct);
				 
				 J2UPPAALConverter converter = new J2UPPAALConverter();
				 converter.writePEA2UppaalFile(dest+".xml", parallel);
				 
				 Vector<Phase> lastStates = this.getLastStates(parallel);
					for (int i= 0; i<lastStates.size(); i++){						
						System.out.println("E<>"+converter.getSystemName()+"."+lastStates.elementAt(i)+"/**/");
					}}
		 
	}
	
	public void getVacuous(RequirementsSet reqSet){		 
		 long start=System.nanoTime();
		 
		 int reqSetSize = reqSet.getReqSetSize();
		 int[] lastStatesPerComponent = new int[reqSetSize];
		 int[] lastStatesInParallelProduct;
		 //PhaseEventAutomata parallel;
		 		 
		 if (reqSetSize <1) {
			 System.out.println("ERROR: There is no requirement in the requirements set");
		 }
		 else		
		 {
			 vacuous = new Vector();
			 //build up an array with the maximal index per component(component==requirement)
			 // and build up parallel automaton 
			 	Vector<PhaseEventAutomata> reqSetAsPEA= reqSet.transformToPEA();
			 	PhaseEventAutomata pea;
			 	int lastState;
			 	pea = reqSetAsPEA.elementAt(0);
				lastState = this.getHighestIndex(pea);
				this.addLastStatesForComp(lastStatesPerComponent, 0, lastState);
			 	parallel = pea;
			 	
				 for (int i=1; i< reqSet.getReqSetSize();i++){
					 pea = reqSetAsPEA.elementAt(i);
					 
					 String dest = "C:/test/vacuous_single"+i+".dot";
					 //dotwriter.write(dest, pea);
					 dest = "C:/test/vacuous_parallel"+i+".dot";
					 //dotwriter.write(dest, parallel);
					 
					 lastState = this.getHighestIndex(pea);
					 this.addLastStatesForComp(lastStatesPerComponent, i, lastState);
					 parallel = parallel.parallel(pea);
					 if (parallel.isEmpty()){
						 reqSet.setInconsistent(true);
						 System.out.println("The requirements set is inconsistent");
						 return;
					 }
					 System.out.println("current nr of states of A_R: "+parallel.getPhases().length);
				 }
				 System.out.println("***********************VACUOUS TEST********************************");
				 //Then get maximal index of the parallel automaton
				 lastStatesInParallelProduct = this.getMaxIndexOfParallelProd(parallel);
				 //Then compare the indices
				 this.compare(lastStatesPerComponent, lastStatesInParallelProduct, reqSet);
				 
				 long dur1=System.nanoTime()-start;
					System.err.println( " Calculation of vacuous consistency check took " );
					System.err.print( ((double)dur1/1000/1000) );
					System.err.println( " m seconds" );
				 
					System.out.println("***********************END VACUOUS TEST********************************");
				 //J2UPPAALConverter converter = new J2UPPAALConverter();
				 //converter.writePEA2UppaalFile("C:/vacuous/testPSSVeto.xml", parallel);
					String dest = "C:/test/vacuous_";
					 //dotwriter.write(dest, parallel);
					J2UPPAALConverter uppaalConverter = new J2UPPAALConverter();
					uppaalConverter.writePEA2UppaalFile(dest+"hybrid2.xml", pea);
		 }
		 
	}
	
	//Precondition: getVacuous(RequirmentsSet reqSet) was called at least once
	public Vector getVacuous() {
		return vacuous;
	}

	private void compare(int[] maxIndexPerComp, int[] maxIndexParallel, RequirementsSet reqSet){
		int size =maxIndexParallel.length;
		this.compare(maxIndexPerComp, maxIndexParallel);
		for (int i=0; i<size; i++){
			if (maxIndexPerComp[i] > maxIndexParallel[i]){
				System.out.println("Requirement "+i+": "+reqSet.getRequirementString(i));
			}
		}
	}
	
	private void compare(int[] maxIndexPerComp, int[] maxIndexParallel){
		int size =maxIndexParallel.length;
		boolean vac = false;
		System.out.println("********RESULT VACUOUS TEST********");
		for (int i=0; i<size; i++){
			if (maxIndexPerComp[i] > maxIndexParallel[i]){
				System.out.println("Requirement "+i+" is only vacuously satisfied in the given requirements set.");
				System.out.println("PhaseNr of requirement that should be reached: "+maxIndexPerComp[i]/2+"; PhaseNr in A_R: "+maxIndexParallel[i]/2);
				
				vacuous.addElement(i);
				vac = true;
			}
		}
		if (vac==false){
			System.out.println("The requirements set is non vacuously consistent");
		}
		System.out.println("********END RESULT VACUOUS TEST********");
	}
	
	private void addLastStatesForComp(int[] list, int compIndex, int lastState){
		if (compIndex > list.length){
			System.out.println("ERROR StronglyVacuous: compIndex>list.length");
		}
		else{
			list[compIndex]=lastState;
		}
	}
	
	
	//berechnet für einen PEA(nicht Parallelprodukt!) den höchsten Index der Locations
	// bsp PEA mit locations st0,st01, st123, st23, st13: --> maxIndex ==4(3+1)
	// bsp PEA mit locations st, stinit --> maxIndex ==0
	public int getHighestIndex(PhaseEventAutomata pea){
		int numberOfStates = getNumberOfStates(pea);
		maxIndex = 0;
		
		for (int i=0; i<numberOfStates; i++){
			Phase location = pea.getPhases()[i];
			PEAPhaseIndexMap map = new PEAPhaseIndexMap(location);	
			if(map.getIndex()>maxIndex){
				maxIndex=map.getIndex();
			}
		}
		return maxIndex;
	}
	
	private int getNumberOfStates(PhaseEventAutomata pea){
		return pea.getPhases().length;
	}
	
	private Phase getState(PhaseEventAutomata pea, int i){
		if (i< getNumberOfStates(pea)){
			return pea.getPhases()[i];
		}
		else if(pea.getPhases().length<=0){
			System.out.println("PEA is empty!");
			return new Phase("error", CDD.FALSE);
		}
		else return pea.getPhases()[0];
	}
	
	private int getIndex(String location){
		PEAPhaseIndexMap map = new PEAPhaseIndexMap(location);
		return map.getIndex();
	}
	
	//berechnet für einen PEA(hier Parallelprodukt!) den höchsten Index der Locations für die einzelnen Komponenten
	// bsp PEA mit locations (st0Xst01) (st123Xst23) (st0Xst13): --> maxIndex ==[4,4](jeweils 3+1)
	// bsp PEA mit locations (stXstinit) --> maxIndex == [0,0]
	public int[] getMaxIndexOfParallelProd(PhaseEventAutomata pea){
		//integer vector, der für das Parallelprodukt der Automaten 
		//je den max index pro Komponente enthält
		int[] maxIndexParallel;		
		int numberOfStates = getNumberOfStates(pea);
		
		//Case i=0 (for initialization)
		Phase state = getState(pea, 0);
		String stateName = state.getName();
		String[] splitted = splitForComponents(stateName);
		maxIndexParallel = new int[splitted.length];
		for (int j=0; j< splitted.length;j++){
			String compLocation = splitted[j];
			int indexCompLocation = getIndex(compLocation);
			maxIndexParallel[j] = indexCompLocation;
		}
		//Case i>0
		for(int i=1; i<numberOfStates; i++){
			state = getState(pea, i);
			stateName = state.getName();
			splitted = splitForComponents(stateName);
			for (int j=0; j< splitted.length;j++){
				String compLocation = splitted[j];
				int indexCompLocation = getIndex(compLocation);
				if (maxIndexParallel[j] < indexCompLocation){
					maxIndexParallel[j] = indexCompLocation;
				}				
			}			
		}		
		return maxIndexParallel;
	}
	
	// Splitted einen String location auf, so dass alle Teile, die durch X abgetrennt sind, 
	// in einen neuen ArrayString gepackt werden		
	private String[] splitForComponents(String location){
		// Create a pattern to match breaks
		//Pattern p = Pattern.compile("(.)*(\\p{Digit})*(X(.)*(\\p{Digit})*)*");
		Pattern p = Pattern.compile("_X_");
        // Split input with the pattern
        String[] result = 
                 p.split(location);
        return result;
    }
	
	
	//wohl nicht benötigt
	//returns the locations of a PEA pea with the highest phase index
	public Vector<Phase> getLastStates(PhaseEventAutomata pea){
		Vector<PEAPhaseIndexMap> indexMap = this.getMapToHighestIndex(pea);
		Vector<Phase> lastStates = new Vector();
		for (int i=0; i<indexMap.size(); i++){
			if (indexMap.elementAt(i).getIndex()==maxIndex){
				lastStates.add(indexMap.elementAt(i).getPhase());
			}
		}
		return lastStates;
	}
	
	//Wohl nicht benötigt
	//berechnet eine map, wo für jede location des peas der höchste phasenindex +1 angegeben wird; 
	//Achtung: st012-->3
	private Vector<PEAPhaseIndexMap> getMapToHighestIndex(PhaseEventAutomata pea){		
		Vector<PEAPhaseIndexMap> indexMap = new Vector();
		int numberOfStates = getNumberOfStates(pea);
		maxIndex = 0;
		
		for (int i=0; i<numberOfStates; i++){
			Phase location = pea.getPhases()[i];
			PEAPhaseIndexMap map = new PEAPhaseIndexMap(location);
			indexMap.addElement(map);			
			if(map.getIndex()>maxIndex){
				maxIndex=map.getIndex();
			}
		}
		return indexMap;		
	}
	
	public void writeParallelProduct(String filedest){
		DOTWriter dotwriter = new DOTWriter(filedest, parallel);
	    dotwriter.write();
	}
	
	public void getAdditionalCheckData(){
		System.out.println("**********ADDITIONAL DATA Vacuous Test**************");
		//STATES
		int numberOfStates = getNumberOfStates(parallel);
		System.out.println("Number of locations in PEA: "+numberOfStates);
		//TRANSITIONS
		int numberOfEdges =0;
		for (int i=0; i< numberOfStates; i++){
			List<Transition> edges =parallel.getLocation(i).getTransitions();
			numberOfEdges= numberOfEdges + edges.size();			
		}
		System.out.println("Number of transitions in PEA: "+numberOfEdges);
		
		
		
		
		

	}
	
	
	
	public void getLastStates2(PhaseEventAutomata pea){
		for (int j=0; j<pea.getNumberOfLocations(); j++){
			int maxIndex= this.getHighestIndex(pea);			
			int index = this.getIndex(pea.getLocation(j).getName());
			if (index == maxIndex){
				System.out.println("E<>"+pea.getName()+"."+pea.getLocation(j).getName());
			}
		}
	}
	

}
