/*
 *
 * This file is part of the PEA tool set
 *
 * The PEA tool set is a collection of tools for
 * Phase Event Automata (PEA). See
 * http://csd.informatik.uni-oldenburg.de/projects/peatools.html
 * for more information.
 *
 * Copyright (C) 2005-2006, Department for Computing Science,
 *                          University of Oldenburg
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA
 */
package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking;

import java.util.HashMap;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseSet;
import de.uni_freiburg.informatik.ultimate.lib.pea.Trace2PeaCompiler;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;

/**
 * The class <code>Compiler</code> offers the functionality needed to construct phase event automate nets as specified
 * in <code>pea.modelchecking.schemas.PEA.xsd</code>. The compilation is done via the public method <code>compile</code>
 * . The class also provides a static main method which takes one, two, or four arguments:
 * <ul>
 * <li>Argument "-tf": XML-file of the formula to compile. It has to match the schema
 * <code>pea.modelchecking.schemas.TestForm.xsd</code>. Argument is required.
 * <li>Argument "-mc": XML-file of the formula in model-checkable form. If the file does not exists the compile will
 * create it. The file matches <code>pea.modelchecking.schemas.ModelCheckForm.xsd</code>. Default value is
 * <i>FileToTranslate </i> <code>_mc.xml</code>, where <i>FileToTranslate </i> is the full path of the file to translate
 * without <code>.xml</code> in the end. Argument is optional.
 * <li>Argument "-pea": Prefix for name-attributes of phase event automata as defined in
 * <code>pea.modelchecking.schemas.PEA.xsd</code>. Several phase event automata are stored in a phase event automata
 * net. Default value is <code>pea</code>. The automata are numbered. Argument is optional.
 * <li>Argument "-net": Prefix of xml-files the generated phase event automata nets are stored in. Default is
 * <code>peaNet</code> and the files are numbered. The compiler will create the files if they are not present. Argument
 * is optional.
 * <li>Argument "-parallel": If set to "true", the parallel composition of all PEAs in a net is computed and saved in a
 * file <code>netName_par.xml</code>. This is done for every net.
 * <li>Argument "-lc": Configuration file to initialise the built in log4j logger. Default value is
 * <code>src/pea/modelchecking/CompilerLog.config</code>. Argument is optional.
 * <li>Argument "-help": Prints the usage of the compiler
 * </ul>
 *
 * @author Roland Meyer
 *
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.schemas
 */
public class Compiler {

	public static final String TESTFORmFILE_ARG = "-tf";
	public static final String MCFORmFILE_ARG = "-mc";
	public static final String PEA_ARG = "-pea";
	public static final String PEANET_ARG = "-net";
	public static final String PARALLEL_ARG = "-parallel";
	public static final String HELP_ARG = "-help";
	public static final String LOG_CONFIG_FILE_ARG = "-lc";
	private static final String LOG_CONFIG_FILE = "src/pea/modelchecking/CompilerLog.config";

	private static final String DEFAULT_LOGGER = "Compiler";
	public static final boolean USE_ZDECISION = true;
	public static final boolean USE_BOOLEANDECISION = false;

	private String peaNetPrefix = "peaNet";
	private String peaPrefix = "pea";

	private ILogger mLogger = null;

	private boolean parallel = false;

	private int peaCounter = 0;
	private int peaNetCounter = 0;

	private TestForm2MCFormCompiler mcFormCompiler = null;
	private MCTraceXML2JConverter traceConverter = null;
	private Trace2PeaCompiler traceCompiler = null;

	private HashMap<Transition, PhaseSet> trans2phases[];
	private Set<String> syncEvents;

	/**
	 * Initialises the Compiler object. Takes as parameter a string that defines the loggername for the built in log4j
	 * logger. If the string is empty, the default name <code>Compiler</code> is used. An application using a Compiler
	 * object has to make sure that the logger is initialised via <code>PropertyConfigurator.configure()</code>.
	 *
	 * @param loggerName
	 * @see ILogger
	 * @see PropertyConfigurator
	 */
	public Compiler(final ILogger logger, final String loggerName, final boolean useZDecision) throws Exception {
		mLogger = logger;
		mcFormCompiler = new TestForm2MCFormCompiler();
		traceConverter = new MCTraceXML2JConverter(useZDecision);
		traceCompiler = new Trace2PeaCompiler(logger);
		new XMLWriter();
	}

	/**
	 * Initialises the Compiler object with the default logger.
	 */
	public Compiler(final ILogger logger, final boolean useZDecision) throws Exception {
		this(logger, "", useZDecision);
	}

	/**
	 * @return an array of transition to phaseset maps (if you call it after calling compile())
	 */
	public HashMap<Transition, PhaseSet>[] getTrans2Phases() {
		return trans2phases;
	}

	/**
	 * Generates a fresh phase event automata name <code>peaprefix+peaCounter</code> and increments the counter
	 *
	 * @return The name
	 */
	private String getFreshPEAName() {
		final String result = peaPrefix + peaCounter;
		peaCounter++;
		return result;
	}

	/**
	 * Generates a fresh phase event automata net name <code>peaNetprefix+peaNetCounter</code> and increments the
	 * counter
	 *
	 * @return The name
	 */
	private String getFreshPEANetName() {
		final String result = peaNetPrefix + peaNetCounter;
		peaNetCounter++;
		return result;
	}

	/**
	 * Collects all events in a given CDD and puts them into the syncEvent member set.
	 *
	 * @param events
	 *            The CDD to be processed.
	 */
	private void collectSyncEvents(final CDD events) {
		if (events == null || events == CDD.TRUE || events == CDD.FALSE) {
			return;
		}
		if (events.getDecision() instanceof EventDecision) {
			syncEvents.add(((EventDecision) events.getDecision()).getEvent());
		}
		for (int i = 0; i < events.getChilds().length; i++) {
			collectSyncEvents(events.getChilds()[i]);
		}
	}

	/**
	 * Sets the prefix for phase event automata net files.
	 *
	 * @param peaNetPrefix
	 *            The peaNetPrefix to set.
	 */
	public void setPeaNetPrefix(final String peaNetPrefix) {
		this.peaNetPrefix = peaNetPrefix;
	}

	/**
	 * Sets the prefix for phase event automata in phase event automata nets
	 *
	 * @param peaPrefix
	 *            The peaPrefix to set.
	 */
	public void setPeaPrefix(final String peaPrefix) {
		this.peaPrefix = peaPrefix;
	}

	/**
	 * Sets the parallel argument for the given phase event automata nets
	 *
	 * @param parallel
	 *            The parallel argument.
	 */
	public void setParallel(final boolean parallel) {
		this.parallel = parallel;
	}

	/**
	 * @return Returns the syncEvents.
	 */
	public Set<String> getSyncEvents() {
		return syncEvents;
	}

	/**
	 * Prints a help-text on how to use the compiler
	 */
	private static void printUse() {
		System.out.println("Usage: java Compiler [" + Compiler.TESTFORmFILE_ARG
				+ " <File of test formula to compile>]\n" + "                     [" + Compiler.MCFORmFILE_ARG
				+ " <File of compiled formula in model checkable form>]\n" + "                     [" + Compiler.PEA_ARG
				+ " <Prefix for peas in peaNet files>]\n" + "                     [" + Compiler.PEANET_ARG
				+ " <Prefix for peaNet files>]\n" + "                     [" + Compiler.PARALLEL_ARG
				+ " <true, if parallel composition needs to be computed>]\n" + "                     ["
				+ Compiler.LOG_CONFIG_FILE_ARG + " <Log configuration file>]\n" + "                     ["
				+ Compiler.HELP_ARG + "]");
		System.out.println("Argument " + Compiler.TESTFORmFILE_ARG + " required");
	}
}
