package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayList;
import java.util.List;
import org.apache.log4j.Logger;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

/**
 * 
 * Parameters are the same as IncrementalInclsuionCheck except for an extra integer parameter.
 * The parameter is used to assign which IncrementalInclusionCheck will be tested.
 * Example: Testing IncrementalInclusionCheck2 -> Jeffery_Test_2(Iservices, sf,
			a, b,2)
			Testing IncrementalInclusionCheck3 -> Jeffery_Test_2(Iservices, sf,
			a, b,3)...
 * 
 * 
 * @author jefferyyjhsu@iis.sinica.edu.tw
 *
 * @param <LETTER>
 * @param <STATE>
 */


public class Jeffery_Test_2<LETTER,STATE> implements IOperation<LETTER,STATE>{

	ArrayList<INestedWordAutomaton<LETTER,STATE>> automataCollection;
	private static Logger s_Logger;
	Boolean result1,result2;
	
	public Jeffery_Test_2(IUltimateServiceProvider services, StateFactory<STATE> sf,
			INestedWordAutomatonSimple<LETTER, STATE> a, List<INestedWordAutomatonSimple<LETTER,STATE>> b,int num) throws AutomataLibraryException{
		switch(num){
		default:
		case 2:
			result1 = (new IncrementalInclusionCheck2<LETTER,STATE>(services,sf,a,b)).getResult();
			IncrementalInclusionCheck2<LETTER,STATE> IIC2 = (new IncrementalInclusionCheck2<LETTER,STATE>(services,sf,a,b.subList(0, 1)));
			for(int i=1;i<b.size();i++){
				IIC2.addSubtrahend(b.get(i));
			}
			result2 = IIC2.getResult();
			break;
		case 3:
			result1 = (new IncrementalInclusionCheck3<LETTER,STATE>(services,sf,a,b)).getResult();
			IncrementalInclusionCheck3<LETTER,STATE> IIC3 = (new IncrementalInclusionCheck3<LETTER,STATE>(services,sf,a,b.subList(0, 1)));
			for(int i=1;i<b.size();i++){
				IIC3.addSubtrahend(b.get(i));
			}
			result2 = IIC3.getResult();
			break;
		case 4:
			result1 = (new IncrementalInclusionCheck4<LETTER,STATE>(services,sf,a,b)).getResult();
			IncrementalInclusionCheck4<LETTER,STATE> IIC4 = (new IncrementalInclusionCheck4<LETTER,STATE>(services,sf,a,b.subList(0, 1)));
			for(int i=1;i<b.size();i++){
				IIC4.addSubtrahend(b.get(i));
			}
			result2 = IIC4.getResult();
			break;
		case 5:
			result1 = (new IncrementalInclusionCheck5<LETTER,STATE>(services,sf,a,b)).getResult();
			IncrementalInclusionCheck5<LETTER,STATE> IIC5 = (new IncrementalInclusionCheck5<LETTER,STATE>(services,sf,a,b.subList(0, 1)));
			for(int i=1;i<b.size();i++){
				IIC5.addSubtrahend(b.get(i));
			}
			result2 = IIC5.getResult();
			break;
		}
	}
		
	
	@Override
	public String operationName() {
		return "Jeffery_Test_2";
	}
	
	@Override
	public String startMessage() {
		return "Start " + operationName();
	}
	
	@Override
	public String exitMessage() {
		return "Exit " + operationName();
	}
	
	@Override
	public Boolean getResult(){
		return (result1.equals(result2));
	}
	/*public String getResult() throws OperationCanceledException {
		return "Jeffery_Test_2_result:"+automataCollection.size();
	}*/
	
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		return true;
	}
	
}
