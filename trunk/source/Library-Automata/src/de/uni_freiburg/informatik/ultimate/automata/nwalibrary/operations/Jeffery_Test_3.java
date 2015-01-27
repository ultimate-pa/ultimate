package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayList;
import java.util.List;
import java.util.Date;
import org.apache.log4j.Logger;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

/**
 * 
 * Parameters are the same as IncrementalInclsuionCheck except for an extra integer parameter.
 * The parameter is used to assign which IncrementalInclusionCheck will be tested.
 * Example: Testing IncrementalInclusionCheck2 -> Jeffery_Test_3(Iservices, sf,
			a, b,2)
			Testing IncrementalInclusionCheck3 -> Jeffery_Test_3(Iservices, sf,
			a, b,3)...
 * 
 * 
 * @author jefferyyjhsu@iis.sinica.edu.tw
 *
 * @param <LETTER>
 * @param <STATE>
 */


public class Jeffery_Test_3<LETTER,STATE> implements IOperation<LETTER,STATE>{
	static long sumNodeInTheEnd1 = 0,sumNodeInTheEnd2 = 0,sumNodeInTheEnd3 = 0,sumNodeInTheEnd4 = 0,sumNodeInTheEnd5 = 0,sumNodeInTheEnd32 = 0,sumNodeInTheEnd42 = 0,sumNodeInTheEnd52 = 0;
	static long sumTotalNode1 = 0,sumTotalNode2 = 0,sumTotalNode3 = 0,sumTotalNode4 = 0,sumTotalNode5 = 0,sumTotalNode32 = 0,sumTotalNode42 = 0,sumTotalNode52 = 0;
	static long sumRun2 = 0,sumRun3 = 0,sumRun4 = 0,sumRun5 = 0,sumRun32 = 0,sumRun42 = 0,sumRun52 = 0;
	static long testnum1 = 0,testnum2 = 0,testnum3 = 0,testnum4 = 0,testnum5 = 0,testnum32 = 0,testnum42 = 0,testnum52 = 0;
	static long time1 = 0,time2 = 0, time3 = 0,time4 = 0, time5 = 0, time32 = 0, time42 = 0, time52 = 0, timeBuffer;
	static boolean init = false;
	
	ArrayList<INestedWordAutomaton<LETTER,STATE>> automataCollection;
	private static Logger s_Logger;
	long avgNodeInTheEnd = 0,avgNodeGenerated = 0,avgRun = 0,testNum;
	long avgTime = 0;
	boolean result;
	public Jeffery_Test_3(IUltimateServiceProvider services, StateFactory<STATE> sf,
			INestedWordAutomatonSimple<LETTER, STATE> a, List<INestedWordAutomatonSimple<LETTER,STATE>> b,int num) throws AutomataLibraryException{
		
		switch(num){
		default:
		case 1:
			timeBuffer = (new Date()).getTime();
			IncrementalInclusionCheckDifference<LETTER,STATE> IIC1 = (new IncrementalInclusionCheckDifference<LETTER,STATE>(services,sf,a,b.subList(0, 1)));
			for(int i=1;i<b.size();i++){
				IIC1.addSubtrahend(b.get(i));
			}
			time1+=(new Date()).getTime()-timeBuffer;
			testnum1++;
			testNum = testnum1;
			sumTotalNode1+=IIC1.size();
			sumNodeInTheEnd1+=IIC1.size();
			avgRun = -1;
			avgNodeGenerated = sumTotalNode1/testNum;
			avgNodeInTheEnd = sumNodeInTheEnd1/testNum;
			avgTime = time1/testNum;
			result = IIC1.getResult();
			break;
		case 2:
			timeBuffer = (new Date()).getTime();
			IncrementalInclusionCheck2<LETTER,STATE> IIC2 = (new IncrementalInclusionCheck2<LETTER,STATE>(services,sf,a,b.subList(0, 1)));
			for(int i=1;i<b.size();i++){
				IIC2.addSubtrahend(b.get(i));
			}
			time2+=(new Date()).getTime()-timeBuffer;
			testnum2++;
			testNum = testnum2;
			sumRun2+=IIC2.counter_run;
			sumTotalNode2+=IIC2.counter_total_nodes;
			sumNodeInTheEnd2+=IIC2.counter_total_nodes;
			avgRun = sumRun2/testNum;
			avgNodeGenerated = sumTotalNode2/testNum;
			avgNodeInTheEnd = sumNodeInTheEnd2/testNum;
			avgTime = time2/testNum;
			result = IIC2.getResult();
			break;
		case 3:
			timeBuffer = (new Date()).getTime();
			IncrementalInclusionCheck3<LETTER,STATE> IIC3 = (new IncrementalInclusionCheck3<LETTER,STATE>(services,sf,a,b.subList(0, 1)));
			for(int i=1;i<b.size();i++){
				IIC3.addSubtrahend(b.get(i));
			}
			time3+=(new Date()).getTime()-timeBuffer;
			testnum3++;
			testNum = testnum3;
			sumRun3+=IIC3.counter_run;
			sumTotalNode3+=IIC3.counter_total_nodes;
			sumNodeInTheEnd3+=IIC3.completeLeafSet.size();
			avgRun = sumRun3/testNum;
			avgNodeGenerated = sumTotalNode3/testNum;
			avgNodeInTheEnd = sumNodeInTheEnd3/testNum;
			avgTime = time3/testNum;
			result = IIC3.getResult();
			break;
		case 4:
			timeBuffer = (new Date()).getTime();
			IncrementalInclusionCheck4<LETTER,STATE> IIC4 = (new IncrementalInclusionCheck4<LETTER,STATE>(services,sf,a,b.subList(0, 1)));
			for(int i=1;i<b.size();i++){
				IIC4.addSubtrahend(b.get(i));
			}
			time4+=(new Date()).getTime()-timeBuffer;
			testnum4++;
			testNum = testnum4;
			sumRun4+=IIC4.counter_run;
			sumTotalNode4+=IIC4.counter_total_nodes;
			sumNodeInTheEnd4+=IIC4.completeLeafSet.size();
			avgRun = sumRun4/testNum;
			avgNodeGenerated = sumTotalNode4/testNum;
			avgNodeInTheEnd = sumNodeInTheEnd4/testNum;
			avgTime = time4/testNum;
			result = IIC4.getResult();
			break;
		case 5:
			timeBuffer = (new Date()).getTime();
			IncrementalInclusionCheck5<LETTER,STATE> IIC5 = (new IncrementalInclusionCheck5<LETTER,STATE>(services,sf,a,b.subList(0, 1)));
			for(int i=1;i<b.size();i++){
				IIC5.addSubtrahend(b.get(i));
			}
			time5+=(new Date()).getTime()-timeBuffer;
			testnum5++;
			testNum = testnum5;
			sumRun5+=IIC5.counter_run;
			sumTotalNode5+=IIC5.counter_total_nodes;
			sumNodeInTheEnd5+=IIC5.completeLeafSet.size();
			avgRun = sumRun5/testNum;
			avgNodeGenerated = sumTotalNode5/testNum;
			avgNodeInTheEnd = sumNodeInTheEnd5/testNum;
			avgTime = time5/testNum;
			result = IIC5.getResult();
			break;
		case 32:
			timeBuffer = (new Date()).getTime();
			IncrementalInclusionCheck3_2<LETTER,STATE> IIC3_2 = (new IncrementalInclusionCheck3_2<LETTER,STATE>(services,sf,a,b.subList(0, 1)));
			for(int i=1;i<b.size();i++){
				IIC3_2.addSubtrahend(b.get(i));
			}
			time32+=(new Date()).getTime()-timeBuffer;
			testnum32++;
			testNum = testnum32;
			sumRun32+=IIC3_2.counter_run;
			sumTotalNode32+=IIC3_2.counter_total_nodes;
			sumNodeInTheEnd32+=IIC3_2.completeLeafSet.size();
			avgRun = sumRun32/testNum;
			avgNodeGenerated = sumTotalNode32/testNum;
			avgNodeInTheEnd = sumNodeInTheEnd32/testNum;
			avgTime = time32/testNum;
			result = IIC3_2.getResult();
			break;
		case 42:
			timeBuffer = (new Date()).getTime();
			IncrementalInclusionCheck4_2<LETTER,STATE> IIC4_2 = (new IncrementalInclusionCheck4_2<LETTER,STATE>(services,sf,a,b.subList(0, 1)));
			for(int i=1;i<b.size();i++){
				IIC4_2.addSubtrahend(b.get(i));
			}
			time42+=(new Date()).getTime()-timeBuffer;
			testnum42++;
			testNum = testnum42;
			sumRun42+=IIC4_2.counter_run;
			sumTotalNode42+=IIC4_2.counter_total_nodes;
			sumNodeInTheEnd42+=IIC4_2.completeLeafSet.size();
			avgRun = sumRun42/testNum;
			avgNodeGenerated = sumTotalNode42/testNum;
			avgNodeInTheEnd = sumNodeInTheEnd42/testNum;
			avgTime = time42/testNum;
			result = IIC4_2.getResult();
			break;
		case 52:
			timeBuffer = (new Date()).getTime();
			IncrementalInclusionCheck5_2<LETTER,STATE> IIC5_2 = (new IncrementalInclusionCheck5_2<LETTER,STATE>(services,sf,a,b.subList(0, 1)));
			for(int i=1;i<b.size();i++){
				IIC5_2.addSubtrahend(b.get(i));
			}
			time52+=(new Date()).getTime()-timeBuffer;
			testnum52++;
			testNum = testnum52;
			sumRun52+=IIC5_2.counter_run;
			sumTotalNode52+=IIC5_2.counter_total_nodes;
			sumNodeInTheEnd52+=IIC5_2.completeLeafSet.size();
			avgRun = sumRun52/testNum;
			avgNodeGenerated = sumTotalNode52/testNum;
			avgNodeInTheEnd = sumNodeInTheEnd52/testNum;
			avgTime = time52/testNum;
			result = IIC5_2.getResult();
			break;
		}
	}
		
	
	@Override
	public String operationName() {
		return "Jeffery_Test_3";
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
	public String getResult(){
		return ("avg Nodes in the end:"+avgNodeInTheEnd+" avg Nodes generated:"+avgNodeGenerated+" avgRuns:"+avgRun+" Total test:"+testNum+" avg Time:"+avgTime+" Result:"+result);
	}
	/*public String getResult() throws OperationCanceledException {
		return "Jeffery_Test_3_result:"+automataCollection.size();
	}*/
	
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		return true;
	}
	
}
