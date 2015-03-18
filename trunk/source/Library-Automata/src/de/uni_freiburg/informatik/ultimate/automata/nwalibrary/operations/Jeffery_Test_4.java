package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Date;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

/**
 * 
 * Parameters are the same as IncrementalInclsuionCheck except for an extra integer parameter.
 * The parameter is used to assign which IncrementalInclusionCheck will be tested.
 * Example: Testing IncrementalInclusionCheck2 -> Jeffery_Test_4(Iservices, sf,
			a, b,2)
			Testing IncrementalInclusionCheck3 -> Jeffery_Test_4(Iservices, sf,
			a, b,3)...
 * 
 * 
 * @author jefferyyjhsu@iis.sinica.edu.tw
 *
 * @param <LETTER>
 * @param <STATE>
 */


public class Jeffery_Test_4<LETTER,STATE> implements IOperation<LETTER,STATE>{
	String folder;
	static long faster_i = 0, slower_i = 0;
	static long timeBuffer1, timeBuffer2;
	public Jeffery_Test_4(IUltimateServiceProvider services, StateFactory<STATE> sf,
			INestedWordAutomatonSimple<LETTER, STATE> a, List<INestedWordAutomatonSimple<LETTER,STATE>> b) throws AutomataLibraryException, IOException{
		folder = "/media/user_data/Java/trunk/examples/Automata/finiteAutomata/incrementalInclusion/randomCasesDumpedResults/";
		timeBuffer1 = (new Date()).getTime();
		IncrementalInclusionCheckDifference<LETTER,STATE> IIC1 = (new IncrementalInclusionCheckDifference<LETTER,STATE>(services,sf,a,b.subList(0, 1)));
		for(int i=1;i<b.size();i++){
			IIC1.addSubtrahend(b.get(i));
		}
		timeBuffer1=(new Date()).getTime()-timeBuffer1;
		timeBuffer2 = (new Date()).getTime();
		IncrementalInclusionCheck4<LETTER,STATE> IIC4 = (new IncrementalInclusionCheck4<LETTER,STATE>(services,sf,a,b.subList(0, 1)));
		for(int i=1;i<b.size();i++){
			IIC4.addSubtrahend(b.get(i));
		}
		timeBuffer2=(new Date()).getTime()-timeBuffer2;
		long x = new Long(timeBuffer1), y = new Long(timeBuffer2);
		if(x==0){
			x=1;
		}
		if(y==0){
			y=1;
		}
		if(y>x*10){
			FileWriter fw = new FileWriter(folder+"faster_"+faster_i+".ats");
			faster_i++;
			BufferedWriter bw = new BufferedWriter(fw);
			bw.write("//Result:"+IIC1.getResult());
			bw.newLine();
			bw.write("//Difference: Time:"+timeBuffer1+" Total states:"+IIC1.size());
			bw.newLine();
			bw.write("//IncrementalInclusionCheck4: Time:"+timeBuffer2+" Total states:"+IIC4.counter_total_nodes+" States in the end:"+IIC4.completeLeafSet.size()+" Run:"+IIC4.counter_run);
			bw.newLine();
			bw.write((new AtsDefinitionPrinter<String, String>(services, "A", a)).getDefinitionAsString());
			bw.newLine();
			int i;
			for(i=0;i<b.size();i++){
				bw.write((new AtsDefinitionPrinter<String, String>(services, "B"+i, b.get(i))).getDefinitionAsString());
				bw.newLine();
			}
			bw.close();
			fw.close();
		}else if(x>y*10){
			FileWriter fw = new FileWriter(folder+"slower_"+slower_i+".ats");
			slower_i++;
			BufferedWriter bw = new BufferedWriter(fw);
			bw.write("//Result:"+IIC1.getResult());
			bw.newLine();
			bw.write("//Difference: Time:"+timeBuffer1+" Total states:"+IIC1.size());
			bw.newLine();
			bw.write("//IncrementalInclusionCheck4: Time:"+timeBuffer2+" Total states:"+IIC4.counter_total_nodes+" States in the end:"+IIC4.completeLeafSet.size()+" Run:"+IIC4.counter_run);
			bw.newLine();
			bw.write((new AtsDefinitionPrinter<String, String>(services, "A", a)).getDefinitionAsString());
			bw.newLine();
			int i;
			for(i=0;i<b.size();i++){
				bw.write((new AtsDefinitionPrinter<String, String>(services, "B"+i, b.get(i))).getDefinitionAsString());
				bw.newLine();
			}
			bw.close();
			fw.close();
		}
		
	}
	
	public Jeffery_Test_4(IUltimateServiceProvider services, StateFactory<STATE> sf,
			INestedWordAutomatonSimple<LETTER, STATE> a, List<INestedWordAutomatonSimple<LETTER,STATE>> b, String folderInput) throws AutomataLibraryException, IOException{
		folder = folderInput;
		timeBuffer1 = (new Date()).getTime();
		IncrementalInclusionCheckDifference<LETTER,STATE> IIC1 = (new IncrementalInclusionCheckDifference<LETTER,STATE>(services,sf,a,b.subList(0, 1)));
		for(int i=1;i<b.size();i++){
			IIC1.addSubtrahend(b.get(i));
		}
		timeBuffer1=(new Date()).getTime()-timeBuffer1;
		timeBuffer2 = (new Date()).getTime();
		IncrementalInclusionCheck4<LETTER,STATE> IIC4 = (new IncrementalInclusionCheck4<LETTER,STATE>(services,sf,a,b.subList(0, 1)));
		for(int i=1;i<b.size();i++){
			IIC4.addSubtrahend(b.get(i));
		}
		timeBuffer2=(new Date()).getTime()-timeBuffer2;
		long x = new Long(timeBuffer1), y = new Long(timeBuffer2);
		if(x==0){
			x=1;
		}
		if(y==0){
			y=1;
		}
		if(y>x*10){
			FileWriter fw = new FileWriter(folder+"faster_"+faster_i+".ats");
			faster_i++;
			BufferedWriter bw = new BufferedWriter(fw);
			bw.write("//Result:"+IIC1.getResult());
			bw.newLine();
			bw.write("//Difference: Time:"+timeBuffer1+" Total states:"+IIC1.size());
			bw.newLine();
			bw.write("//IncrementalInclusionCheck4: Time:"+timeBuffer2+" Total states:"+IIC4.counter_total_nodes+" States in the end:"+IIC4.completeLeafSet.size()+" Run:"+IIC4.counter_run);
			bw.newLine();
			bw.write((new AtsDefinitionPrinter<String, String>(services, "A", a)).getDefinitionAsString());
			bw.newLine();
			int i;
			for(i=0;i<b.size();i++){
				bw.write((new AtsDefinitionPrinter<String, String>(services, "B"+i, b.get(i))).getDefinitionAsString());
				bw.newLine();
			}
			bw.close();
			fw.close();
		}else if(x>y*10){
			FileWriter fw = new FileWriter(folder+"slower_"+slower_i+".ats");
			slower_i++;
			BufferedWriter bw = new BufferedWriter(fw);
			bw.write("//Result:"+IIC1.getResult());
			bw.newLine();
			bw.write("//Difference: Time:"+timeBuffer1+" Total states:"+IIC1.size());
			bw.newLine();
			bw.write("//IncrementalInclusionCheck4: Time:"+timeBuffer2+" Total states:"+IIC4.counter_total_nodes+" States in the end:"+IIC4.completeLeafSet.size()+" Run:"+IIC4.counter_run);
			bw.newLine();
			bw.write((new AtsDefinitionPrinter<String, String>(services, "A", a)).getDefinitionAsString());
			bw.newLine();
			int i;
			for(i=0;i<b.size();i++){
				bw.write((new AtsDefinitionPrinter<String, String>(services, "B"+i, b.get(i))).getDefinitionAsString());
				bw.newLine();
			}
			bw.close();
			fw.close();
		}
		
	}
	
	@Override
	public String operationName() {
		return "Jeffery_Test_4";
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
		String log = "Output cases:\r\nfaster:"+faster_i+"\r\nslower:"+slower_i;
		return log;
	}
	/*public String getResult() throws OperationCanceledException {
		return "Jeffery_Test_4_result:"+automataCollection.size();
	}*/
	
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return true;
	}
	
}
