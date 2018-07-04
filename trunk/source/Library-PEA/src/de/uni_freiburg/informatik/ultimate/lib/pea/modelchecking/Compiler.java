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

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.PEANet;
import de.uni_freiburg.informatik.ultimate.lib.pea.PEATestAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
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
	private PEAJ2XMLConverter peaConverter = null;

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
	public Compiler(ILogger logger, final String loggerName, final boolean useZDecision) throws Exception {
		mLogger = logger;
		mcFormCompiler = new TestForm2MCFormCompiler();
		traceConverter = new MCTraceXML2JConverter(useZDecision);
		traceCompiler = new Trace2PeaCompiler(logger);
		peaConverter = new PEAJ2XMLConverter();
		new XMLWriter();
	}

	/**
	 * Initialises the Compiler object with the default logger.
	 */
	public Compiler(ILogger logger, final boolean useZDecision) throws Exception {
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
	 * Constructs several phase event automata nets (test automata) from a given test formula.
	 * <p>
	 * The transformation is done in several steps:
	 * <ul>
	 * <li>The test formula is transformed into a formula in model-checkable form. This mcForm document is stored in the
	 * xml-file given by <code>mcFile</code>. If this argument is empty the file <i>file </i> <code>_mc.xml</code> will
	 * be chosen, where <i>file </i> is the file without <code>.xml</code> in the end.
	 * <p>
	 * The compilation to model-checkable form generates the following files:
	 * <ul>
	 * <li><i>file </i> <code>_bin.xml</code> which contains the file but the tree structure resolved to binary trees.
	 * <li><i>file </i> <code>_sync.xml</code> which contains the file <i>file </i> <code>_bin.xml</code> with chops
	 * replaced by sync events
	 * <li><i>file </i> <code>_nf.xml</code> which contains the file <i>file </i> <code>_sync.xml</code> but converted
	 * to almost normal form, this means disjunction is the top level operator, followed by conjunction, followed by
	 * sync events.
	 * <li><code>mcFile</code> which contains the model-checkable form of <code>file</code>. For every disjunction a new
	 * <code>mcForm</code> tree is created. The file satisfies <code>pea.modelchecking.schemas.ModelCheckForm.xsd</code>
	 * .
	 * </ul>
	 * <li>Every <code>mcForm</code> in <code>mcFile</code> is converted into an array of <code>MCTrace</code> java
	 * objects.
	 * <li>All <code>MCTrace</code> objects are converted into <code>PhaseEventAutomata</code> objects.
	 * <li>For every <code>mcForm</code> the phase event automata are written into a file <i>peaNetPrefix </i>
	 * <code>i.xml</code>, where <i>peaNetPrefix </i> is the attribute of the object and <code>i</code> is the index of
	 * the model-checkable form starting with 0.
	 * </ul>
	 * 
	 * @param file
	 *            File of the test formula to compile into phase event automata nets. Needs to satisfy
	 *            <code>pea.modelchecking.schemas.TestForm.xsd</code>.
	 * @param mcFile
	 *            XML-file where the model-checkable form of <code>file</code> is stored. Satisfies
	 *            <code>pea.modelchecking.schemas.ModelCheckForm.xsd</code>.
	 * @return Returns an ArrayList containing Arrays with all generated test automata. The automata in one Array are
	 *         considered to run in parallel.
	 * @throws Exception
	 *             See exceptions in
	 *             <ul>
	 *             <li><code>TestForm2MCFormCompiler</code>, constructor and <code>compile</code> method
	 *             <li><code>MCTraceXML2JConverter</code>, constructor and <code>convert</code> method
	 *             <li><code>PEAJ2XMLConverter</code>, constructor
	 *             <li><code>XMLWriter</code>, <code>writeXMLDocumentToFile</code> method
	 *             </ul>
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.schemas
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.MCTrace
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.TestForm2MCFormCompiler
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.MCTraceXML2JConverter
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.Trace2PeaCompiler
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.PEAJ2XMLConverter
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.XMLWriter
	 */
	public ArrayList<PEATestAutomaton[]> compile(final String file, final String mcFile) throws Exception {

		final ArrayList<PEATestAutomaton[]> resultList = new ArrayList<PEATestAutomaton[]>();
		syncEvents = new HashSet<String>();

		PEATestAutomaton[] peas = null;
		final String fileParent = new File(file).getParent();

		final long startTime = System.currentTimeMillis();

		final Document document = mcFormCompiler.compile(file, mcFile);
		final long durNormalForm = System.currentTimeMillis() - startTime;

		final NodeList mcFormNodes = document.getElementsByTagName(XMLTags.MCFORmTAG);
		final int mcFormsCount = mcFormNodes.getLength();
		for (int i = 0; i < mcFormsCount; i++) {
			final MCTrace[] traces = traceConverter.convert((Element) mcFormNodes.item(i));
			peas = new PEATestAutomaton[traces.length];
			@SuppressWarnings("unchecked")
			final HashMap<Transition, PhaseSet> t2p[] = (HashMap<Transition, PhaseSet>[]) new HashMap<?, ?>[traces.length];
			trans2phases = t2p;
			for (int j = 0; j < traces.length; j++) {
				peas[j] = traceCompiler.compile(getFreshPEAName(), traces[j]);
				trans2phases[j] = traceCompiler.getTrans2Phases(traces[j].getTrace().getPhases());
				collectSyncEvents(traceCompiler.getEntrySync());
				collectSyncEvents(traceCompiler.getExitSync());
			}
			final String actNetName = getFreshPEANetName();
			if (parallel) {
				PEATestAutomaton result = peas[0];
				for (int k = 1; k < peas.length; k++) {
					result = result.parallel(peas[k]);
				}
				String parallelFile;
				if (fileParent != null) {
					parallelFile = fileParent;
					parallelFile += "/" + actNetName + "_par.xml";
				} else {
					parallelFile = actNetName + "_par.xml";
				}
				final PEANet temp = new PEANet();
				temp.addPEA(result);
				peaConverter.convert(temp, parallelFile);
			}
			String peaNetFile = fileParent != null ? fileParent + "/" : "";
			peaNetFile += actNetName + ".xml";

			final List<PEATestAutomaton> tempList = Arrays.asList(peas);
			final ArrayList<PhaseEventAutomata> peaList = new ArrayList<PhaseEventAutomata>(tempList);
			final PEANet peaNet = new PEANet();
			peaNet.setPeas(peaList);

			peaConverter.convert(peaNet, peaNetFile);
			resultList.add(peas);
		}

		mLogger.info("Duration Compilation NormalForm = " + durNormalForm + "(ms)");
		final long durPEAs = System.currentTimeMillis() - startTime - durNormalForm;
		mLogger.info("Duration Compilation PEAS       = " + durPEAs + "(ms)");
		mLogger.info("Duration Compilation            = " + (durPEAs + durNormalForm) + "(ms)");
		return resultList;
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
	 * Starts the compiler
	 * 
	 * @param args
	 *            Parameters to start the compiler. The class description tells the use.
	 */
	public static void main(final String[] args) {
		if (args.length < 1) {
			Compiler.printUse();
			return;
		}

		String logConfigFile = Compiler.LOG_CONFIG_FILE;
		String testFormFile = null;
		String mcFormFile = "";
		String pea = "";
		String peaNet = "";
		String parallel = "";

		for (int i = 0; i < args.length; i++) {
			if (args[i].equals(Compiler.LOG_CONFIG_FILE_ARG)) {
				logConfigFile = args[++i];
			} else if (args[i].equals(Compiler.TESTFORmFILE_ARG)) {
				testFormFile = args[++i];
			} else if (args[i].equals(Compiler.MCFORmFILE_ARG)) {
				mcFormFile = args[++i];
			} else if (args[i].equals(Compiler.PEA_ARG)) {
				pea = args[++i];
			} else if (args[i].equals(Compiler.PEANET_ARG)) {
				peaNet = args[++i];
			} else if (args[i].equals(Compiler.PARALLEL_ARG)) {
				parallel = args[++i];
			} else if (args[i].equals(Compiler.HELP_ARG)) {
				Compiler.printUse();
				return;
			} else {
				Compiler.printUse();
				return;
			}
		}

		Compiler compiler = null;
		try {
			compiler = new Compiler(ILogger.getLogger(Compiler.DEFAULT_LOGGER), false);
		} catch (final Exception e) {
			System.err.println("Compiler could not be initialised");
			e.printStackTrace();
		}

		if (!pea.equals("")) {
			compiler.setPeaPrefix(pea);
		}
		if (!peaNet.equals("")) {
			compiler.setPeaNetPrefix(peaNet);
		}
		if (parallel.equals("true")) {
			compiler.setParallel(true);
		}

		if (testFormFile == null) {
			Compiler.printUse();
			System.out.println("The test formula argument is missing.");
			return;
		} else {
			try {
				compiler.compile(testFormFile, mcFormFile);

			} catch (final Exception e) {
				System.err.println(
				        "Compilation failed. Please consult " + "log file and error message for further details.");
				e.printStackTrace();
				return;
			}
		}
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
