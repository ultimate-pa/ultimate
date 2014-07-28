package de.uni_freiburg.informatik.ultimate.LTL2aut;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

import org.apache.commons.io.IOUtils;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.AstNode;
import de.uni_freiburg.informatik.ultimate.LTL2aut.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;

/**
 * This class handles the communication of with the external tool for
 * translating an LTL formula into a Promela never claim and can parse that
 * claim into an AST.
 * 
 * @author Langenfeld
 * 
 */

public class WrapLTL2Never {

	private final Logger mLogger;

	public WrapLTL2Never(Logger logger) {
		mLogger = logger;
	}

	/**
	 * Returns a B�chi automaton for the ltl formula as a promela never claim.
	 * 
	 * @param ltlFomula
	 *            ltl formula in the form accepted by the called tool
	 * @throws IOException
	 * @throws InterruptedException
	 * @return whole return string of the called tool
	 */
	public String execLTLXBA(String ltlFormula) throws IOException, InterruptedException {
		UltimatePreferenceStore prefs = new UltimatePreferenceStore(Activator.PLUGIN_ID);
		String result = "";

		String line;
		// TODO: fixme, no hard coded arguements!!
		ProcessBuilder pb = new ProcessBuilder(new String[] {
				prefs.getString(PreferenceInitializer.LABEL_TOOLLOCATION), "-f",
				prefs.getString(PreferenceInitializer.LABEL_TOOLARGUMENT).replace("$1", ltlFormula) });
		Process p = pb.start();
		BufferedReader bri = new BufferedReader(new InputStreamReader(p.getInputStream()));

		while ((line = bri.readLine()) != null) {
			// System.out.println(line);
			result += line;
		}
		bri.close();
		p.waitFor();

		return result;
	}

	/**
	 * Returns the Ast of the Promela never claim description of the B�chi
	 * automaton returned by the ltl2b�chi tool.
	 * 
	 * @param ltlFormula
	 *            ltl formula in the format accepted by the tool
	 * @return Ast of B�chi automaton description
	 * @throws Exception
	 */
	public AstNode ltl2Ast(String ltlFormula) throws Exception {
		String toolOutput = this.execLTLXBA(ltlFormula.trim());
		mLogger.debug(String.format("LTLXBA said: %s", toolOutput));
		InputStreamReader file = new InputStreamReader(IOUtils.toInputStream(toolOutput));

		AstNode n = null;
		Lexer lexer = new Lexer(file);
		Parser p = new Parser(lexer);
		n = (AstNode) p.parse().value;

		return n;
	}

}
