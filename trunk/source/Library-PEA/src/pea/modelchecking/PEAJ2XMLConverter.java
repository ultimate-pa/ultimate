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
package pea.modelchecking;

import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;
import org.apache.log4j.PropertyConfigurator;

import pea.CDD;
import pea.PEANet;
import pea.Phase;
import pea.PhaseEventAutomata;
import pea.Transition;
import pea.util.z.ZWrapper;


/**
 * The class <code>PEAJ2XMLConverter</code> takes the given Java
 * <code>PhaseEventAutomata</code> object and generates a corresponding XML
 * PEA elements
 * 
 * @see pea.PhaseEventAutomata
 * @see <code>PEA.xsd</code>
 * 
 * @author Roland Meyer
 */
public class PEAJ2XMLConverter {

    protected static final String DEFAULT_LOGGER = "PEAJ2XMLConverter";

    protected Logger logger = null;

    protected FormulaJ2XMLConverter formulaConverter = null;

    protected FileWriter writer;

    protected List<String> events = null;

    protected List<String> clocks = null;

    //Variables taken from the variable list from PhaseEventAutomata
    protected Map<String,String> variables = null;
    
    //Variables collected via FormulaJ2XMLConverter.convertFast from rangeExpressions 
    @Deprecated     
    protected List<String> rangeVariables = null;

    //Additional variables. Deprecated, use variables from PhaseEventAutomata instead.
    @Deprecated 
    protected ArrayList[] additionalVariables = null;
    
    @Deprecated 
    protected ArrayList[] additionalTypes = null;

    protected int peaCounter = 0;

    protected static final String Z_NAMESPACE = "xmlns=\"http://czt.sourceforge.net/zml\"";

    /**
     * Initialises the PEAJ2XMLConverter object. Takes as parameter a string
     * that defines the loggername for the built in log4j logger. If the string
     * is empty, the default name <code>PEAJ2XMLConverter</code> is used. An
     * application using a PEAJ2XMLConverter object has to make sure that the
     * logger is initialised via <code>PropertyConfigurator.configure()</code>.
     * 
     * @param loggerName
     * @see Logger
     * @see PropertyConfigurator
     */
    public PEAJ2XMLConverter(String loggerName) throws Exception {
        if (loggerName.equals("")) {
            this.logger = Logger
                    .getLogger(PEAJ2XMLConverter.DEFAULT_LOGGER);
        } else {
            this.logger = Logger.getLogger(loggerName);
        }

        this.formulaConverter = new FormulaJ2XMLConverter();

        this.clocks = new ArrayList<String>();
        this.events = new ArrayList<String>();
        this.rangeVariables = new ArrayList<String>();
        this.variables = new HashMap<String,String>();
    }

    /**
     * Initialises the PEAJ2XMLConverter object with the default logger.
     */
    public PEAJ2XMLConverter() throws Exception {
        this("");
    }

    public void convert(PEANet peanet, String file) {
        PhaseEventAutomata[] peas = new PhaseEventAutomata[0];
        peas = peanet.getPeas().toArray(peas);
        ArrayList<String> declarations = peanet.getDeclarations();
        try {
            // peas[0].dump();
            peaCounter = 0;
            this.writer = new FileWriter(file);
            if (peas.length == 0) {
                throw new RuntimeException(
                        "The array of peas is not allowed to be empty");
            }

            writer
                    .write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
                            + "<peaNet xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\""
                            + " xsi:noNamespaceSchemaLocation=\"../schemas/PEA.xsd\">\n");

            writeTypeDeclarations(declarations, this.writer);
            for (int i = 0; i < peas.length; i++) {
                logger.info("Trying to create peaNode " + i);
                createPhaseEventAutomaton(peas[i]);
                logger.info("Creating peaNode " + i + " successful");
                peaCounter++;
            }

            writer.write("</peaNet>\n");

            writer.flush();
            writer.close();
        } catch (Exception e) {
            System.out.println("Errors writing the XML representation of pea");
            e.printStackTrace();
        }
    }

    protected void writeTypeDeclarations(List<String> declarations,
            FileWriter writer) {
        String vardecl;
        try {

            writer.write("<declaration>\n");

            createStandardTypes(writer);
            for (String term : declarations) {
                vardecl = ZWrapper.INSTANCE.declToZml(term);
                this.logger
                        .info("Creating ZML <VarDecl> out of the Term object");
                writer.write(vardecl);
            }

            writer.write("</declaration>\n");

        } catch (Exception e) {
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
    protected void createStandardTypes(FileWriter writer) {
//        try {
//            // true is defined as the empty _schema_
//            writer.write("<ConstDecl " + Z_NAMESPACE + " >\n");
//            writer.write("<DeclName>\n");
//            writer.write("<Word>true</Word>\n");
//            writer.write("</DeclName>\n");
//            writer.write("<SchExpr>\n <SchText/>\n </SchExpr>\n");
//            writer.write("</ConstDecl>\n");
//
//            // false is defined as the empty _set_
//            writer.write("<ConstDecl " + Z_NAMESPACE + " >\n");
//            writer.write("<DeclName>\n");
//            writer.write("<Word>false</Word>\n");
//            writer.write("</DeclName>\n");
//            writer.write("<RefExpr>\n ");
//            writer.write("<RefName>\n");
//            writer.write("<Word>\u2205</Word>\n");
//            writer.write("</RefName>\n");
//            writer.write("</RefExpr>\n");
//            writer.write("</ConstDecl>\n");
//
//            // BOOLEAN is defined as : {true, false}
//            writer.write("<VarDecl " + Z_NAMESPACE + " >\n");
//
//            writer.write("<DeclName>\n");
//            writer.write("<Word>BOOLEAN</Word>\n");
//            writer.write("</DeclName>\n");
//
//            writer.write("<SetExpr>\n ");
//
//            writer.write("<RefExpr>\n ");
//            writer.write("<RefName>\n");
//            writer.write("<Word>true</Word>\n");
//            writer.write("</RefName>\n");
//            writer.write("</RefExpr>\n ");
//
//            writer.write("<RefExpr>\n ");
//            writer.write("<RefName>\n");
//            writer.write("<Word>false</Word>\n");
//            writer.write("</RefName>\n");
//            writer.write("</RefExpr>\n ");
//
//            writer.write("</SetExpr>\n ");
//            writer.write("</VarDecl>\n");
//
//        } catch (IOException e) {
//            System.out
//                    .println("An error occured while creating the standard types!");
//            e.printStackTrace();
//        }
    }

    protected void createPhaseEventAutomaton(PhaseEventAutomata pea)
            throws IOException {
        if (pea.getPhases().length == 0) {
            throw new RuntimeException(
                    "PEA with phase count = 0 is not allowed");
        }
        if (pea.getInit().length == 0) {
            throw new RuntimeException(
                    "PEA with initial phase count = 0 is not allowed");
        }

        this.clocks.clear();
        this.events.clear();
        
        // TODO: the collection of range variables does not work correctly because there is no type declarations
        // are lacking. Use the variable list of PhaseEventAutomata instead.
        this.rangeVariables.clear();
        this.variables = pea.getVariables();

        writer.write("<pea name=\"" + pea.getName() + "\">\n");
        
        // Create local declarations
        if(pea.getDeclarations() != null)
            writeTypeDeclarations(pea.getDeclarations(),writer);

        // Create phase nodes
        writer.write("<phases>\n");
        Phase[] phases = pea.getPhases();
        Phase[] init = pea.getInit();
        List<Phase> temp = new LinkedList<Phase>(Arrays.asList(phases));
        temp.removeAll(Arrays.asList(init));
        Phase[] notInitPhases = (Phase[]) temp.toArray(new Phase[0]);

        for (int i = 0; i < init.length; i++) {
            this.createPhaseNode(init[i], true);
        }
        for (int i = 0; i < notInitPhases.length; i++) {
            this.createPhaseNode(notInitPhases[i], false);
        }
        writer.write("</phases>\n");

        // Create transition nodes
        if (peaHasTransitions(pea)) {
            writer.write("<transitions>\n");
            for (int i = 0; i < phases.length; i++) {
                List transitions = phases[i].getTransitions();
                Iterator transIter = transitions.iterator();
                while (transIter.hasNext()) {
                    Transition trans = (Transition) transIter.next();
                    createTransitionNode(trans);

                }
            }
            writer.write("</transitions>\n");
        }

        // Add additional variables to var list.
        if (this.variables!=null && !this.variables.isEmpty()
                || (this.additionalVariables != null && !this.additionalVariables[peaCounter]
                        .isEmpty())) {
            writer.write("<variables>\n");
            if (this.additionalVariables != null
                    && !this.additionalVariables[peaCounter].isEmpty()) {
                Iterator addVarIterator = this.additionalVariables[peaCounter]
                        .iterator();
                Iterator typesIterator = this.additionalTypes[peaCounter]
                        .iterator();
                while (addVarIterator.hasNext()) {
                    String actVariable = (String) addVarIterator.next();
                    String typeName = (String) typesIterator.next();
                    writer.write("<variable name=\"" + actVariable
                            + "\" type=\"" + typeName + "\"/>");
                }
            }
            if (!this.variables.isEmpty()) {
                Iterator variablesIterator = this.variables.keySet().iterator();
                while (variablesIterator.hasNext()) {
                    String actVariable = (String) variablesIterator.next();
                    writer.write("<variable name=\"" + actVariable
                            + "\" type=\"" + variables.get(actVariable) + "\"/>");
                }
            }
            if (!this.rangeVariables.isEmpty()) {
                Iterator rvariablesIterator = this.rangeVariables.iterator();
                while (rvariablesIterator.hasNext()) {
                    String actRVariable = (String) rvariablesIterator.next();
                    if(!variables.containsKey(actRVariable))
                        writer.write("<variable name=\"" + actRVariable
                                + "\" type=\"default\"/>");
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
        this.clocks.removeAll(this.rangeVariables);

        if (!this.clocks.isEmpty()) {
            writer.write("<clocks>\n");
            Iterator clocksIterator = this.clocks.iterator();
            while (clocksIterator.hasNext()) {
                String actClock = (String) clocksIterator.next();
                writer.write("<clock name=\"" + actClock + "\"/>\n");
            }
            writer.write("</clocks>\n");
        }

        if (!this.events.isEmpty()) {
            writer.write("<events>\n");
            Iterator eventsIterator = this.events.iterator();
            while (eventsIterator.hasNext()) {
                String actEvent = (String) eventsIterator.next();
                writer.write("<event name=\"" + actEvent + "\"/>\n");
            }
            writer.write("</events>\n");
        }

        writer.write("</pea>\n");

    }

    private boolean peaHasTransitions(PhaseEventAutomata pea) {
        Phase[] phases = pea.getPhases();
        for (int i = 0; i < phases.length; i++) {
            if (phases[i].getTransitions().size() > 0) {
                return true;
            }
        }
        return false;
    }

    protected void createPhaseNode(Phase phase, boolean init)
            throws IOException {
        this.writer.write("<phase name=\"" + phase.getName() + "\" >\n");

        // if this phase is an initial phase, create the initial tag
        if (init) {
            this.writer.write("<initial/>\n");
        }
        this.writer.write("<invariant>\n");
        this.writer.write(this.formulaConverter.convertFast(phase
                .getStateInvariant(), this.rangeVariables, this.events));
        this.writer.write("</invariant>\n");
        if (phase.getClockInvariant() != CDD.TRUE) {
            this.writer.write("<clockInvariant>\n");
            this.writer.write(this.formulaConverter.convertFast(phase
                    .getClockInvariant(), this.clocks, this.events));
            this.writer.write("</clockInvariant>\n");
        }
        this.writer.write("</phase>\n");
    }

    protected void createTransitionNode(Transition trans) throws IOException {
        String source = trans.getSrc().getName();
        String dest = trans.getDest().getName();
        this.logger.info("Creating transition from " + source + " to " + dest);
        
        
        String guardsDNFResolved = formulaConverter.formulaToXML(trans
                .getGuard(), clocks, events);
        
            //{ "\nblubb und test\n" } ; 
            
            //formulaConverter.getDisjuncts(trans
            //    .getGuard(), clocks, events);
        String resetString = "";
        String[] resets = trans.getResets();
        for (int i = 0; i < resets.length; i++) {
            resetString += "<reset name=\"" + resets[i] + "\"/>\n";
            if (!clocks.contains(resets[i])) {
                clocks.add(resets[i]);
            }
        }

            writer.write("<transition source = \"" + source + "\" target = \""
                    + dest + "\">\n");
            writer.write("<guard>\n");
            writer.write(guardsDNFResolved);
            writer.write("</guard>\n");
            writer.write(resetString);
            writer.write("</transition>\n");
    }

    /**
     * Deprecated. Please use variable list in PEA instead.
     * @param additionalVariables
     *            Sets the list of additional variables that has to be inserted
     *            to the output-document.
     */
    @Deprecated
    public void setAdditionalVariables(ArrayList[] additionalVariables) {
        this.additionalVariables = additionalVariables;
    }

    /**
     * Deprecated. Please use types list in PEA instead.
     * @param types
     *            Sets the types belonging to additionalVariables.
     */
    @Deprecated
    public void setAdditionalTypes(ArrayList[] types) {
        this.additionalTypes = types;
    }

    public static void main(String[] args) {
        try {
            PEAXML2JConverter xml2j = new PEAXML2JConverter(false);
            PhaseEventAutomata[] peas = xml2j
                    .convert("./pea/modelchecking/CaseStudy/ComNW.xml");
            PEANet peanet = new PEANet();
            List<PhaseEventAutomata> peaL = Arrays.asList(peas);
            ArrayList<PhaseEventAutomata> peaList = new ArrayList<PhaseEventAutomata>(
                    peaL);

            peanet.setPeas(peaList);
            PEAJ2XMLConverter j2XMLFast = new PEAJ2XMLConverter();
            j2XMLFast.convert(peanet, "./pea/modelchecking/example/test.xml");
            peas = xml2j.convert("./pea/modelchecking/example/test.xml");
        } catch (Exception e) {
            System.out.println("Outermost exception");
            e.printStackTrace();
        }
    }
}
