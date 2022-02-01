/* $Id: PEAJ2XMLConverter.java 397 2009-06-23 11:48:29Z jfaber $
 *
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

import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.PEANet;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;
import de.uni_freiburg.informatik.ultimate.lib.pea.util.z.ZWrapper;

/**
 * The class <code>PEAJ2XMLConverter</code> takes the given Java <code>PhaseEventAutomata</code> object and generates a
 * corresponding XML PEA elements
 *
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata
 * @see <code>PEA.xsd</code>
 *
 * @author Roland Meyer
 */
public class PEAJ2XMLConverter {

	protected static final String DEFAULT_LOGGER = "PEAJ2XMLConverter";

	protected ILogger logger = null;

	protected FormulaJ2XMLConverter formulaConverter = null;

	protected FileWriter writer;

	protected List<String> events = null;

	protected List<String> clocks = null;

	// Variables taken from the variable list from PhaseEventAutomata
	protected Map<String, String> variables = null;

	// Variables collected via FormulaJ2XMLConverter.convertFast from rangeExpressions
	@Deprecated
	protected List<String> rangeVariables = null;

	// Additional variables. Deprecated, use variables from PhaseEventAutomata instead.
	@Deprecated
	protected ArrayList[] additionalVariables = null;

	@Deprecated
	protected ArrayList[] additionalTypes = null;

	protected int peaCounter = 0;

	protected static final String Z_NAMESPACE = "xmlns=\"http://czt.sourceforge.net/zml\"";

	/**
	 * Initialises the PEAJ2XMLConverter object. Takes as parameter a string that defines the loggername for the built
	 * in log4j logger. If the string is empty, the default name <code>PEAJ2XMLConverter</code> is used. An application
	 * using a PEAJ2XMLConverter object has to make sure that the logger is initialised via
	 * <code>PropertyConfigurator.configure()</code>.
	 * 
	 * @param loggerName
	 * @see ILogger
	 * @see PropertyConfigurator
	 */
	public PEAJ2XMLConverter(final String loggerName) throws Exception {
		if (loggerName.equals("")) {
			logger = ILogger.getLogger(PEAJ2XMLConverter.DEFAULT_LOGGER);
		} else {
			logger = ILogger.getLogger(loggerName);
		}

		formulaConverter = new FormulaJ2XMLConverter();

		clocks = new ArrayList<>();
		events = new ArrayList<>();
		rangeVariables = new ArrayList<>();
		variables = new HashMap<>();
	}

	/**
	 * Initialises the PEAJ2XMLConverter object with the default logger.
	 */
	public PEAJ2XMLConverter() throws Exception {
		this("");
	}

	public void convert(final PEANet peanet, final String file) {
		PhaseEventAutomata[] peas = new PhaseEventAutomata[peanet.getPeas().size()];
		peas = peanet.getPeas().toArray(peas);
		final ArrayList<String> declarations = peanet.getDeclarations();
		try {
			// peas[0].dump();
			peaCounter = 0;
			writer = new FileWriter(file);
			if (peas.length == 0) {
				throw new RuntimeException("The array of peas is not allowed to be empty");
			}

			writer.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
			        + "<peaNet xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\""
			        + " xsi:noNamespaceSchemaLocation=\"../schemas/PEA.xsd\">\n");

			writeTypeDeclarations(declarations, writer);
			for (int i = 0; i < peas.length; i++) {
				logger.info("Trying to create peaNode " + i);
				createPhaseEventAutomaton(peas[i]);
				logger.info("Creating peaNode " + i + " successful");
				peaCounter++;
			}

			writer.write("</peaNet>\n");

			writer.flush();
			writer.close();
		} catch (final Exception e) {
			System.out.println("Errors writing the XML representation of pea");
			e.printStackTrace();
		}
	}

	protected void writeTypeDeclarations(final List<String> declarations, final FileWriter writer) {
		String vardecl;
		try {

			writer.write("<declaration>\n");

			createStandardTypes(writer);
			for (final String term : declarations) {
				vardecl = ZWrapper.INSTANCE.declToZml(term);
				logger.info("Creating ZML <VarDecl> out of the Term object");
				writer.write(vardecl);
			}

			writer.write("</declaration>\n");

		} catch (final Exception e) {
			System.out.println("Errors writing the Type declarations to XML");
			e.printStackTrace();
		}
	}

	/**
	 * Noop
	 * 
	 * @param writer
	 * @deprecated
	 */
	@Deprecated
	protected void createStandardTypes(final FileWriter writer) {
		// try {
		// // true is defined as the empty _schema_
		// writer.write("<ConstDecl " + Z_NAMESPACE + " >\n");
		// writer.write("<DeclName>\n");
		// writer.write("<Word>true</Word>\n");
		// writer.write("</DeclName>\n");
		// writer.write("<SchExpr>\n <SchText/>\n </SchExpr>\n");
		// writer.write("</ConstDecl>\n");
		//
		// // false is defined as the empty _set_
		// writer.write("<ConstDecl " + Z_NAMESPACE + " >\n");
		// writer.write("<DeclName>\n");
		// writer.write("<Word>false</Word>\n");
		// writer.write("</DeclName>\n");
		// writer.write("<RefExpr>\n ");
		// writer.write("<RefName>\n");
		// writer.write("<Word>\u2205</Word>\n");
		// writer.write("</RefName>\n");
		// writer.write("</RefExpr>\n");
		// writer.write("</ConstDecl>\n");
		//
		// // BOOLEAN is defined as : {true, false}
		// writer.write("<VarDecl " + Z_NAMESPACE + " >\n");
		//
		// writer.write("<DeclName>\n");
		// writer.write("<Word>BOOLEAN</Word>\n");
		// writer.write("</DeclName>\n");
		//
		// writer.write("<SetExpr>\n ");
		//
		// writer.write("<RefExpr>\n ");
		// writer.write("<RefName>\n");
		// writer.write("<Word>true</Word>\n");
		// writer.write("</RefName>\n");
		// writer.write("</RefExpr>\n ");
		//
		// writer.write("<RefExpr>\n ");
		// writer.write("<RefName>\n");
		// writer.write("<Word>false</Word>\n");
		// writer.write("</RefName>\n");
		// writer.write("</RefExpr>\n ");
		//
		// writer.write("</SetExpr>\n ");
		// writer.write("</VarDecl>\n");
		//
		// } catch (IOException e) {
		// System.out
		// .println("An error occured while creating the standard types!");
		// e.printStackTrace();
		// }
	}

	protected void createPhaseEventAutomaton(final PhaseEventAutomata pea) throws IOException {
		if (pea.getPhases().length == 0) {
			throw new RuntimeException("PEA with phase count = 0 is not allowed");
		}
		if (pea.getInit().length == 0) {
			throw new RuntimeException("PEA with initial phase count = 0 is not allowed");
		}

		clocks.clear();
		events.clear();

		// TODO: the collection of range variables does not work correctly because there is no type declarations
		// are lacking. Use the variable list of PhaseEventAutomata instead.
		rangeVariables.clear();
		variables = pea.getVariables();

		writer.write("<pea name=\"" + pea.getName() + "\">\n");

		// Create local declarations
		if (pea.getDeclarations() != null) {
			writeTypeDeclarations(pea.getDeclarations(), writer);
		}

		// Create phase nodes
		writer.write("<phases>\n");
		final Phase[] phases = pea.getPhases();
		final Phase[] init = pea.getInit();
		final List<Phase> temp = new LinkedList<>(Arrays.asList(phases));
		temp.removeAll(Arrays.asList(init));
		final Phase[] notInitPhases = temp.toArray(new Phase[temp.size()]);

		for (int i = 0; i < init.length; i++) {
			createPhaseNode(init[i], true);
		}
		for (int i = 0; i < notInitPhases.length; i++) {
			createPhaseNode(notInitPhases[i], false);
		}
		writer.write("</phases>\n");

		// Create transition nodes
		if (peaHasTransitions(pea)) {
			writer.write("<transitions>\n");
			for (int i = 0; i < phases.length; i++) {
				final List transitions = phases[i].getTransitions();
				final Iterator transIter = transitions.iterator();
				while (transIter.hasNext()) {
					final Transition trans = (Transition) transIter.next();
					createTransitionNode(trans);

				}
			}
			writer.write("</transitions>\n");
		}

		// Add additional variables to var list.
		if (variables != null && !variables.isEmpty()
		        || (additionalVariables != null && !additionalVariables[peaCounter].isEmpty())) {
			writer.write("<variables>\n");
			if (additionalVariables != null && !additionalVariables[peaCounter].isEmpty()) {
				final Iterator addVarIterator = additionalVariables[peaCounter].iterator();
				final Iterator typesIterator = additionalTypes[peaCounter].iterator();
				while (addVarIterator.hasNext()) {
					final String actVariable = (String) addVarIterator.next();
					final String typeName = (String) typesIterator.next();
					writer.write("<variable name=\"" + actVariable + "\" type=\"" + typeName + "\"/>");
				}
			}
			if (!variables.isEmpty()) {
				final Iterator<String> variablesIterator = variables.keySet().iterator();
				while (variablesIterator.hasNext()) {
					final String actVariable = variablesIterator.next();
					writer.write(
					        "<variable name=\"" + actVariable + "\" type=\"" + variables.get(actVariable) + "\"/>");
				}
			}
			if (!rangeVariables.isEmpty()) {
				final Iterator<String> rvariablesIterator = rangeVariables.iterator();
				while (rvariablesIterator.hasNext()) {
					final String actRVariable = rvariablesIterator.next();
					if (!variables.containsKey(actRVariable)) {
						writer.write("<variable name=\"" + actRVariable + "\" type=\"default\"/>");
					}
				}
			}
			writer.write("</variables>\n");
		}

		// A name appearing in a range expression of a (state)invariant
		// is added to the variables list as the clocks are treated in the
		// clock invariant. For guards there is no separation between clock
		// and variable range expressions, thus all names are added to the
		// clocks list and those that have been recognised to be variables
		// are removed with this statement.
		clocks.removeAll(rangeVariables);

		if (!clocks.isEmpty()) {
			writer.write("<clocks>\n");
			final Iterator<String> clocksIterator = clocks.iterator();
			while (clocksIterator.hasNext()) {
				final String actClock = clocksIterator.next();
				writer.write("<clock name=\"" + actClock + "\"/>\n");
			}
			writer.write("</clocks>\n");
		}

		if (!events.isEmpty()) {
			writer.write("<events>\n");
			final Iterator<String> eventsIterator = events.iterator();
			while (eventsIterator.hasNext()) {
				final String actEvent = eventsIterator.next();
				writer.write("<event name=\"" + actEvent + "\"/>\n");
			}
			writer.write("</events>\n");
		}

		writer.write("</pea>\n");

	}

	private boolean peaHasTransitions(final PhaseEventAutomata pea) {
		final Phase[] phases = pea.getPhases();
		for (int i = 0; i < phases.length; i++) {
			if (phases[i].getTransitions().size() > 0) {
				return true;
			}
		}
		return false;
	}

	protected void createPhaseNode(final Phase phase, final boolean init) throws IOException {
		writer.write("<phase name=\"" + phase.getName() + "\" >\n");

		// if this phase is an initial phase, create the initial tag
		if (init) {
			writer.write("<initial/>\n");
		}
		writer.write("<invariant>\n");
		writer.write(formulaConverter.convertFast(phase.getStateInvariant(), rangeVariables, events));
		writer.write("</invariant>\n");
		if (phase.getClockInvariant() != CDD.TRUE) {
			writer.write("<clockInvariant>\n");
			writer.write(formulaConverter.convertFast(phase.getClockInvariant(), clocks, events));
			writer.write("</clockInvariant>\n");
		}
		writer.write("</phase>\n");
	}

	protected void createTransitionNode(final Transition trans) throws IOException {
		final String source = trans.getSrc().getName();
		final String dest = trans.getDest().getName();
		logger.info("Creating transition from " + source + " to " + dest);

		final String guardsDNFResolved = formulaConverter.formulaToXML(trans.getGuard(), clocks, events);

		// { "\nblubb und test\n" } ;

		// formulaConverter.getDisjuncts(trans
		// .getGuard(), clocks, events);
		String resetString = "";
		final String[] resets = trans.getResets();
		for (int i = 0; i < resets.length; i++) {
			resetString += "<reset name=\"" + resets[i] + "\"/>\n";
			if (!clocks.contains(resets[i])) {
				clocks.add(resets[i]);
			}
		}

		writer.write("<transition source = \"" + source + "\" target = \"" + dest + "\">\n");
		writer.write("<guard>\n");
		writer.write(guardsDNFResolved);
		writer.write("</guard>\n");
		writer.write(resetString);
		writer.write("</transition>\n");
	}

	/**
	 * Deprecated. Please use variable list in PEA instead.
	 * 
	 * @param additionalVariables
	 *            Sets the list of additional variables that has to be inserted to the output-document.
	 */
	@Deprecated
	public void setAdditionalVariables(final ArrayList[] additionalVariables) {
		this.additionalVariables = additionalVariables;
	}

	/**
	 * Deprecated. Please use types list in PEA instead.
	 * 
	 * @param types
	 *            Sets the types belonging to additionalVariables.
	 */
	@Deprecated
	public void setAdditionalTypes(final ArrayList[] types) {
		additionalTypes = types;
	}

	public static void main(final String[] args) {
		try {
			final PEAXML2JConverter xml2j = new PEAXML2JConverter(false);
			PhaseEventAutomata[] peas = xml2j.convert("./pea/modelchecking/CaseStudy/ComNW.xml");
			final PEANet peanet = new PEANet();
			final List<PhaseEventAutomata> peaL = Arrays.asList(peas);
			final ArrayList<PhaseEventAutomata> peaList = new ArrayList<>(peaL);

			peanet.setPeas(peaList);
			final PEAJ2XMLConverter j2XMLFast = new PEAJ2XMLConverter();
			j2XMLFast.convert(peanet, "./pea/modelchecking/example/test.xml");
			peas = xml2j.convert("./pea/modelchecking/example/test.xml");
		} catch (final Exception e) {
			System.out.println("Outermost exception");
			e.printStackTrace();
		}
	}
}
