package de.uni_freiburg.informatik.ultimate.lib.pea.reqcheck;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Vector;

import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;

public class TransformPEAStateNames {

	
	
	
	public Vector<String[]> buildTable(final PhaseEventAutomata pea){
		final Vector<String[]> nameTable = new Vector();
		final Phase[] phases = pea.getPhases();
		for (int i=0; i<phases.length;i++){
			final Phase phase = phases[i];
			final String oldName = phase.getName();
			final String newName = "st"+i;
			final String[] nameAssignment = addNameAssignment(oldName, newName);
			nameTable.add(nameAssignment);
			
		}
		return nameTable;
	}
	
	public void transform(final Vector<String[]> nameTable, final String fileInput, final String fileOutput){
		    
		    try {
		      //use buffering, reading one line at a time
		      //FileReader always assumes default encoding is OK!
		    		
		      final BufferedReader input =  new BufferedReader(new FileReader(fileInput));
		      final BufferedWriter writer =	new BufferedWriter(new FileWriter(fileOutput));
		      
		      try {
		        String line = null; //not declared within while loop
		        /*
		        * readLine is a bit quirky :
		        * it returns the content of a line MINUS the newline.
		        * it returns null only for the END of the stream.
		        * it returns an empty String if two newlines appear in a row.
		        */
		        while (( line = input.readLine()) != null){
		        	String lineString = line;
		        	for (int i=0; i<nameTable.size(); i++){
		    			final String[] nameAssignment = nameTable.elementAt(i);
		    			final String oldName = getOldName(nameAssignment);
		    			final String newName = getNewName(nameAssignment);
		    			
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
		    catch (final IOException ex){
		      ex.printStackTrace();
		    }


		
		
	}
	
	private String[] addNameAssignment(final String oldName, final String newName){
		final String[] nameAssignment = new String[2];
		nameAssignment[0] = oldName;
		nameAssignment[1] = newName;
		return nameAssignment;
	}
	
	private String getOldName(final String[] nameAssignment){
		final String oldName = nameAssignment[0];
		return oldName;
	}
	
	private String getNewName(final String[] nameAssignment){
		final String newName = nameAssignment[1];
		return newName;
	}
	
	public static void main(final String[] args) {
		// TODO Auto-generated method stub
		final TestPatternToPEA patternToPEA = new TestPatternToPEA();
		
		final PhaseEventAutomata pea = patternToPEA.vacuousTest2();
		final PhaseEventAutomata pea2 = patternToPEA.vacuousTest2();
		final TransformPEAStateNames transformer = new TransformPEAStateNames();
		final Vector<String[]> nameTable = transformer.buildTable(pea);
		transformer.transform(nameTable, "C:/vacuous/vac2_12.xml", "C:/vacuous/vac2_12neu.xml");
		
		final String test ="st0_X_st0 && st0";
		final String t = "st0";
		System.out.println(test.contains(t));
		System.out.println(test.replace(t, "stA"));
		
	}
	
}
