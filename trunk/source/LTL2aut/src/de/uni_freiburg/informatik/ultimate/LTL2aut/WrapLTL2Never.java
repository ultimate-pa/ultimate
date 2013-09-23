package de.uni_freiburg.informatik.ultimate.LTL2aut;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;

import org.apache.commons.io.IOUtils;

import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.AstNode;

/*
 * Abstracts the file system acces and third party program 
 * acces. 
 */

public class WrapLTL2Never {
	
	
	//protected static Logger Logger = UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	/**
	 * location of the ltl to Büchi tool
	 */
	public File toolLocatoin = new File("C:\\ltl2ba.exe");
	/**
	 * Command line options to start the ltl to Büchi tool.
	 * Use $1 as a placeholder for the ltl formula.
	 */
	public String commandLineArgument = " -f \" $1 \"";
	

	
	/**
	 * Returns a Büchi automaton for the ltl formula as a promela never claim.
	 * 
	 * @param ltlFomula ltl formula in the form accepted by the underlying tool
	 * @throws IOException 
	 * @throws InterruptedException 
	 */
	public String execLTLXBA(String ltlFormula) throws IOException, InterruptedException
	{
		String result = "";
		
	      String line;
	      Process p = Runtime.getRuntime().exec(this.toolLocatoin + this.commandLineArgument.replace("$1", ltlFormula));
	      BufferedReader bri = new BufferedReader
	        (new InputStreamReader(p.getInputStream()));
	      
	      while ((line = bri.readLine()) != null) {
	        //System.out.println(line);
	        result += line;
	      }
	      bri.close();
	      p.waitFor();
	    
	    return result;
	}
	
	public AstNode ltl2Ast(String ltlFormula) throws Exception
	{
		String toolOutput = this.execLTLXBA(ltlFormula);
		System.out.println(toolOutput);
		InputStreamReader file = new InputStreamReader(IOUtils.toInputStream(toolOutput));
		
		AstNode n = null;
		//try
			Lexer lexer = new Lexer(file);
			parser p = new parser(lexer);
			n = (AstNode)p.parse().value;

		
		return n;
	}
	
}

































