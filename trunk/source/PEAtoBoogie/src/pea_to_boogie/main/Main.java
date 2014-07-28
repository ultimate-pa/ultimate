package pea_to_boogie.main;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogieOutput;

import pea.PhaseEventAutomata;
import pea.modelchecking.PEAXML2JConverter;
import pea_to_boogie.translator.Translator;
import req_to_pea.ReqToPEA;
import srParse.srParsePattern;
public class Main{

	public static void main (String args[]) {
		 if (args.length < 2) {
			 System.err.println("USAGE: pea_to_boogie.main file.req {file.bpl combinationNumber | file.xml}");
			 return;
		 }

 		 Translator translator = new Translator();
    	 
	     if (args[0].endsWith(".req") && args[1].endsWith(".bpl") && args.length == 3) {
	    	 String reqFilePath = args[0];
	         String boogieFilePath = args[1];
	         int combinationNum = Integer.parseInt(args[2]);
			 srParsePattern[] patterns = new ReqToPEA().genPatterns(reqFilePath);
	         if (!(1 <= combinationNum & combinationNum <= patterns.length)) {
	        	 throw new IllegalArgumentException("The valid range of combinationNum is integers in [1, pea.length].");
	         }
	    	 translator.setCombinationNum(combinationNum);
	    	 Unit unit = translator.genBoogie(patterns);	
	    	 try {
	    		 PrintWriter pWriter = new PrintWriter(new FileWriter(boogieFilePath));
	    		 BoogieOutput boogie_out = new BoogieOutput(pWriter);
		         boogie_out.printBoogieProgram(unit);
		    	 System.out.println("==================================================");
		    	 System.out.println("Translation to Boogie code in "+args[1]+" is done!");
		    	 System.out.println("==================================================");
	    	 } catch (IOException ex) {
	    		 ex.printStackTrace();
	    	 }
	     } else if (args[0].endsWith(".req") && args[1].endsWith(".xml")) {
	    	 String reqFilePath = args[0];
	    	 String xmlFilePath = args[1];
			 srParsePattern[] patterns = new ReqToPEA().genPatterns(reqFilePath);
	    	 new ReqToPEA().genPEAforUPPAAL(patterns, xmlFilePath);
	    	 System.out.println("==================================================");
	    	 System.out.println("Translation to Uppaal xml in "+args[1]+" is done!");
	    	 System.out.println("==================================================");
	     } else if (args[0].endsWith(".xml") && args[1].endsWith(".bpl") && args.length == 3) {
	    	 String peaFilePath = args[0];
	         int combinationNum = Integer.parseInt(args[2]);
	         try {
	        	 PEAXML2JConverter xml2jconverter = new PEAXML2JConverter(false);           
	        	 PhaseEventAutomata[] pea = xml2jconverter.convert(peaFilePath);
	        	 if (!(1 <= combinationNum & combinationNum <= pea.length)) {
	        		 throw new IllegalArgumentException("The valid range of combinationNum is integers in [1, pea.length].");
	        	 }
	        	 translator.setCombinationNum(combinationNum);
	        	 translator.genBoogie(pea);	
	         } catch (Exception e) {
	        	 e.printStackTrace();
	         }
	     } else {
	    	 System.err.println("USAGE: pea_to_boogie.main file.req {file.bpl combinationNumber | file.xml}");
	     }
  	 
    }	
}


