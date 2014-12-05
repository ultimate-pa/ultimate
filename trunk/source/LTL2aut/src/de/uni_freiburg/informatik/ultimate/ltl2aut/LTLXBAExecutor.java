package de.uni_freiburg.informatik.ultimate.ltl2aut;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import org.apache.commons.io.IOUtils;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.core.util.MonitoredProcess;
import de.uni_freiburg.informatik.ultimate.ltl2aut.ast.AstNode;
import de.uni_freiburg.informatik.ultimate.ltl2aut.preferences.PreferenceInitializer;

/**
 * This class handles the communication of with the external tool for
 * translating an LTL formula into a Promela never claim and can parse that
 * claim into an AST.
 * 
 * @author Langenfeld
 * 
 */

public class LTLXBAExecutor {

	private final Logger mLogger;
	private final IUltimateServiceProvider mServices;
	private final IToolchainStorage mStorage;

	public LTLXBAExecutor(IUltimateServiceProvider services, IToolchainStorage storage) {
		mServices = services;
		mStorage = storage;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	/**
	 * Returns the AST of the Promela never claim description of the Büchi
	 * automaton returned by the ltl2büchi tool.
	 * 
	 * @param ltlFormula
	 *            LTL formula in the format accepted by the tool
	 * @return AST of Büchi automaton description
	 * @throws Exception
	 */
	public AstNode ltl2Ast(String ltlFormula) throws Exception {
		String toolOutput = execLTLXBA(ltlFormula.trim());
		mLogger.debug(String.format("LTLXBA said: %s", toolOutput));
		InputStreamReader file = new InputStreamReader(IOUtils.toInputStream(toolOutput));
		try {
			return (AstNode) new Parser(new Lexer(file)).parse().value;
		} catch (Exception ex) {
			StringBuilder sb = new StringBuilder();
			sb.append("Exception during parsing of LTLXBA output:");
			sb.append(CoreUtil.getPlatformLineSeparator());
			sb.append(ex.getMessage());
			sb.append(CoreUtil.getPlatformLineSeparator());
			sb.append("Tool said:");
			sb.append(CoreUtil.getPlatformLineSeparator());
			sb.append(toolOutput);
			mLogger.fatal(sb.toString());
			throw new Exception(sb.toString());
		}
	}

	/**
	 * Returns a Büchi automaton for the ltl formula as a promela never claim.
	 * 
	 * @param ltlFomula
	 *            ltl formula in the form accepted by the called tool
	 * @throws IOException
	 * @throws InterruptedException
	 * @return whole return string of the called tool
	 */
	private String execLTLXBA(String ltlFormula) throws IOException, InterruptedException {
		String[] command = getCommand(ltlFormula);
		MonitoredProcess process = MonitoredProcess.exec(command, null, null, mServices, mStorage);
		String rtr = convertStreamToString(process.getInputStream());
		process.waitfor();
		return rtr;
	}

	private static String convertStreamToString(InputStream is) {
		BufferedReader reader = new BufferedReader(new InputStreamReader(is));
		StringBuilder out = new StringBuilder();
		String line;
		try {
			while ((line = reader.readLine()) != null) {
				out.append(line).append(CoreUtil.getPlatformLineSeparator());
			}
			reader.close();
		} catch (IOException e) {
		}
		return out.toString();
	}

	private String[] getCommand(String ltlFormula) {
		UltimatePreferenceStore prefs = new UltimatePreferenceStore(Activator.PLUGIN_ID);
		ltlFormula = prefs.getString(PreferenceInitializer.LABEL_TOOLARGUMENT).replace("$1", ltlFormula);
		ltlFormula = ltlFormula.replaceAll("\\(", " ( ");
		ltlFormula = ltlFormula.replaceAll("\\)", " ) ");
		ltlFormula = ltlFormula.replaceAll("\\s+", " ");
		List<String> rtr = new ArrayList<>();
		rtr.add(prefs.getString(PreferenceInitializer.LABEL_TOOLLOCATION));
		rtr.add("-f");
		rtr.add(ltlFormula);
		return rtr.toArray(new String[0]);
	}

}
