/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2015 Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 *
 * This file is part of the ULTIMATE LTL2Aut plug-in.
 *
 * The ULTIMATE LTL2Aut plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LTL2Aut plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LTL2Aut plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LTL2Aut plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LTL2Aut plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.ltl2aut;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import org.apache.commons.io.IOUtils;

import de.uni_freiburg.informatik.ultimate.core.lib.util.MonitoredProcess;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ltl2aut.ast.AstNode;
import de.uni_freiburg.informatik.ultimate.ltl2aut.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * This class handles the communication of with the external tool for translating an LTL formula into a Promela never
 * claim and can parse that claim into an AST.
 *
 * @author Langenfeld
 */

public class LTLXBAExecutor {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final IToolchainStorage mStorage;

	public LTLXBAExecutor(final IUltimateServiceProvider services, final IToolchainStorage storage) {
		mServices = services;
		mStorage = storage;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	/**
	 * Returns the AST of the Promela never claim description of the Büchi automaton returned by the ltl2büchi tool.
	 *
	 * @param ltlFormula
	 *            LTL formula in the format accepted by the tool
	 * @return AST of Büchi automaton description
	 * @throws Exception
	 */
	public AstNode ltl2Ast(final String ltlFormula) throws Exception {
		final String toolOutput = execLTLXBA(ltlFormula.trim());
		mLogger.debug(String.format("LTLXBA said: %s", toolOutput));
		final InputStreamReader file = new InputStreamReader(IOUtils.toInputStream(toolOutput));
		try {
			return (AstNode) new Parser(new Lexer(file)).parse().value;
		} catch (final Exception ex) {
			mLogger.fatal("Exception during parsing of LTLXBA output for formula " + ltlFormula, ex);
			mLogger.fatal("Tool said:");
			mLogger.fatal(toolOutput);
			throw ex;
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
	private String execLTLXBA(final String ltlFormula) throws IOException, InterruptedException {
		final String[] command = getCommand(ltlFormula);
		final MonitoredProcess process = MonitoredProcess.exec(command, null, null, mServices, mStorage);
		final String rtr = convertStreamToString(process.getInputStream());
		process.waitfor();
		return rtr;
	}

	private static String convertStreamToString(final InputStream is) {
		final BufferedReader reader = new BufferedReader(new InputStreamReader(is));
		final StringBuilder out = new StringBuilder();
		String line;
		try {
			while ((line = reader.readLine()) != null) {
				out.append(line).append(CoreUtil.getPlatformLineSeparator());
			}
			reader.close();
		} catch (final IOException e) {
		}
		return out.toString();
	}

	private String[] getCommand(String ltlFormula) {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		ltlFormula = prefs.getString(PreferenceInitializer.LABEL_TOOLARGUMENT).replace("$1", ltlFormula);
		ltlFormula = ltlFormula.replaceAll("\\(", " ( ");
		ltlFormula = ltlFormula.replaceAll("\\)", " ) ");
		ltlFormula = ltlFormula.replaceAll("\\s+", " ");
		final List<String> rtr = new ArrayList<>();
		rtr.add(prefs.getString(PreferenceInitializer.LABEL_TOOLLOCATION));
		rtr.add("-f");
		rtr.add(ltlFormula);
		return rtr.toArray(new String[rtr.size()]);
	}

}
