package de.uni_freiburg.informatik.ultimate.LTL2aut;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;

import org.apache.commons.io.IOUtils;

import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.AstNode;
import de.uni_freiburg.informatik.ultimate.LTL2aut.preferences.PreferencePage;

/**
 * This class handles the communication of with the external tool 
 * for translating an LTL formula into a Promela never claim and 
 * can parse that claim into an AST.
 * 
 * @author Langenfeld
 *
 */

public class WrapLTL2Never {
	
	
	//protected static Logger Logger = UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	/**
	 * location of the ltl to Büchi tool
	 */
	//public File toolLocatoin = new File("C:\\ltl2ba.exe");
	/**
	 * Command line options to start the ltl to Büchi tool.
	 * Use $1 as a placeholder for the ltl formula.
	 */
	//public String commandLineArgument = " -f \" $1 \"";
	
	/**
	 * Returns a Büchi automaton for the ltl formula as a promela never claim.
	 * 
	 * @param ltlFomula ltl formula in the form accepted by the called tool
	 * @throws IOException 
	 * @throws InterruptedException 
	 * @return whole return string of the called tool
	 */
	public String execLTLXBA(String ltlFormula) throws IOException, InterruptedException
	{
		String result = "";
		
	      String line;
	      Process p = Runtime.getRuntime().exec( PreferencePage.TOOLLOCATION + PreferencePage.COMMANDLINEARGUMENT.replace("$1", ltlFormula));
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
	
	/**
	 * Returns the Ast of the Promela never claim description of 
	 * the Büchi automaton returned by the ltl2büchi tool.
	 * @param ltlFormula ltl formula in the format accepted by the tool
	 * @return Ast of Büchi automaton description
	 * @throws Exception
	 */
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

































