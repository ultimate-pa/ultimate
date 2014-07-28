package pea.reqCheck;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Vector;


import pea.Phase;
import pea.PhaseEventAutomata;

public class TransformPEAStateNames {

	
	
	
	public Vector<String[]> buildTable(PhaseEventAutomata pea){
		Vector<String[]> nameTable = new Vector();
		Phase[] phases = pea.getPhases();
		for (int i=0; i<phases.length;i++){
			Phase phase = phases[i];
			String oldName = phase.getName();
			String newName = "st"+i;
			String[] nameAssignment = addNameAssignment(oldName, newName);
			nameTable.add(nameAssignment);	
			
		}
		return nameTable;
	}
	
	public void transform(Vector<String[]> nameTable, String fileInput, String fileOutput){
		    
		    try {
		      //use buffering, reading one line at a time
		      //FileReader always assumes default encoding is OK!
		    		
		      BufferedReader input =  new BufferedReader(new FileReader(fileInput));
		      BufferedWriter writer =	new BufferedWriter(new FileWriter(fileOutput));
		      
		      try {
		        String line = null; //not declared within while loop
		        /*
		        * readLine is a bit quirky :
		        * it returns the content of a line MINUS the newline.
		        * it returns null only for the END of the stream.
		        * it returns an empty String if two newlines appear in a row.
		        */
		        while (( line = input.readLine()) != null){
		        	String lineString = line.toString();
		        	for (int i=0; i<nameTable.size(); i++){
		    			String[] nameAssignment = nameTable.elementAt(i);
		    			String oldName = getOldName(nameAssignment);
		    			String newName = getNewName(nameAssignment);    			
		    			
		    			if ((lineString.contains("\""+oldName+"\"")) || (lineString.contains(">"+oldName+"<"))){
		    				lineString = lineString.replace(oldName, newName);
		    			}
		    		}
		          writer.write(lineString);
		          writer.newLine();
		          writer.flush();
		        }
		      }
		      finally {
		        input.close();
		        writer.close();
		        System.out.println(fileInput+" successfully transformed to "+ fileOutput);
		      }
		    }
		    catch (IOException ex){
		      ex.printStackTrace();
		    }


		
		
	}
	
	private String[] addNameAssignment(String oldName, String newName){
		String[] nameAssignment = new String[2];
		nameAssignment[0] = oldName;
		nameAssignment[1] = newName;
		return nameAssignment;
	}
	
	private String getOldName(String[] nameAssignment){
		String oldName = nameAssignment[0];
		return oldName;
	}
	
	private String getNewName(String[] nameAssignment){
		String newName = nameAssignment[1];
		return newName;
	}
	
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		TestPatternToPEA patternToPEA = new TestPatternToPEA();
		
		PhaseEventAutomata pea = patternToPEA.vacuousTest2();
		PhaseEventAutomata pea2 = patternToPEA.vacuousTest2();
		TransformPEAStateNames transformer = new TransformPEAStateNames();
		Vector<String[]> nameTable = transformer.buildTable(pea);
		transformer.transform(nameTable, "C:/vacuous/vac2_12.xml", "C:/vacuous/vac2_12neu.xml");
		
		String test ="st0_X_st0 && st0";
		String t = "st0";
		System.out.println(test.contains(t));
		System.out.println(test.replace(t, "stA"));
		
	}
	
}
