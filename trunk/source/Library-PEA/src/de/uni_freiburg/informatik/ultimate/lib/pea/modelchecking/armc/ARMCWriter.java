/* $Id$
 *
 * This file is part of the PEA tool set
 * 
 * The PEA tool set is a collection of tools for Phase Event Automata
 * (PEA).
 * 
 * Copyright (C) 2005-2006, Carl von Ossietzky University of Oldenburg
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

package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.armc;

import java.io.FileWriter;
import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.PEATestAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.RelationDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.PEA2TCSConverter;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.TCSWriter;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.PEA2TCSConverter.TransitionConstraint;

/**
 * ARMCWriter is a TCSWriter to write ARMC output. It is used by PEA2TCSConverter
 * to translate PEA into ARMC syntax.
 *
 * @author jfaber
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.PEA2TCSConverter
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.TCSWriter
 */
public class ARMCWriter extends TCSWriter {

    public static class ARMCString {
        public static final String ARMC_PRIME = "P";
        public static final String ARMC_US = "_";
        public static final String ERROR_LOC = "error";
        public static final String INIT_LOC = "init";
        public static final String LOC_PREFIX = "p";
        public static final String STATE_NAME = "state";
        public static final String PRIME = "'";
        public static final String LESS = "<";
        public static final String GREATER = ">";
        public static final String LEQ = "=<";
        public static final String GEQ = ">=";
        public static final String EQUALS = "=";
        public static final String NEQ = "!=";
        public static final String PLUS = "+";
        public static final String MINUS = "-";
        public static final String MULT = "*";
        public static final String DIV = "/";

    }
    

    /**
     * A list of primed variables in ARMC representation.
     */
    protected String primedVarList;

    /**
     * A list of unprimed variables in ARMC representation.
     */
    protected String varList;

    /**
     * A flag indicating whether locations names have to be renamed or not.
     */
    protected boolean rename;
    
    /**
     * Maps names of PEA locations to the names of the corresponding locations
     * in the resulting ARMC transition system.
     */
    protected Map<String,String> renameMap;

    /**
     * In ARMC output every transition gets a number stored in this counter.
     */
    protected int transCounter = 0;

    /**
     * FileWriter to output file.
     */
    protected FileWriter writer;

    /**
     * For ARMC constraints have to be sorted between update constraints (primed) and
     * guard constraints (unprimed). primedWriter is used to write the former.
     */
    private Writer primedWriter;

    /**
     * For ARMC constraints have to be sorted between update constraints (primed) and
     * guard constraints (unprimed). primedWriter is used to write the latter.
     */
    private Writer unPrimedWriter;

    /**
     *  Flag indicating that a primed transition constraint is the first in a
     *  comma separated list.
     */
    private boolean firstPrimedConstraint;

    /**
     *  Flag indicating that a unprimed transition constraint is the first in a
     *  comma separated list.
     */
    private boolean firstUnPrimedConstraint;
    
    
    /**
     * Constructor setting the file name of the output ARMC file.
     * @param fileName
     *          the output file name
     */
    public ARMCWriter(final String fileName) {
        super(fileName);
    }

    /**
     * Constructor setting output file name and rename flag that indicates
     * whether original location names have to be used or whether the locations
     * are renamed into default names.
     * 
     * @param file
     * @param rename
     */
    public ARMCWriter(final String file, final boolean rename) {
        this(file);
        this.rename = rename;
    }

    /**
     * Initialises the members of this class.
     */
    protected void init() {
        renameMap = new HashMap<>();
    }

    /* (non-Javadoc)
     * @see pea.modelchecking.TCSWriter#write()
     */
    @Override
    public void write() {
        try {
            writer = new FileWriter(fileName);
            init();
            writePreamble();
            writeInitialTransitions();
            writeTransitions();
            writer.flush();
            writer.close();
        } catch (final IOException e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * Writes the preamble belonging to ARMC files into the output file.
     * @throws IOException
     *          exception thrown by the output file writer
     */
    protected void writePreamble() throws IOException {
        writer
            .write("% Preamble:\n\n"
                        + ":- multifile r/5,implicit_updates/0,var2names/2,preds/2,cube_size/1,start/1,error/1,refinement/1.\n"
                        + "refinement(inter).\ncube_size(1).\n"
                        + "start(pc("
                        + ARMCString.INIT_LOC
                        +")).\n" + "error(pc("
                        + ARMCString.ERROR_LOC
                        + ")).\n\n\n");

        /* Build varList and primedVarList
         * TODO: Handle declarations in ARMC export
         * */
        final StringBuilder varListBuilder = new StringBuilder();
        final StringBuilder primedVarListBuilder = new StringBuilder();
        for (final Iterator<String> i = converter.getVariables().keySet().iterator(); i.hasNext();) {
            final String variable = i.next();
            varListBuilder.append(ARMCString.ARMC_US + variable);
            primedVarListBuilder.append(ARMCString.ARMC_US + variable + ARMCString.ARMC_PRIME);
            if(i.hasNext()){
                varListBuilder.append(", ");
                primedVarListBuilder.append(", ");
            }
        }
        varList = varListBuilder.toString();
        primedVarList = primedVarListBuilder.toString();
        
        writer.write("preds(p(_, data(");
        writer.write(varList);
        writer.write(")), []).\n\n");

        // Write Var2Names lists
        writer.write("var2names(p(_, data(" +
                varList
                + ")),\n   [");
        for (final Iterator<String> i = converter.getVariables().keySet().iterator(); i.hasNext();) {
            final String var = i.next();
            writer.write("(" + ARMCString.ARMC_US + var + ", '" + var + "')");
            if(i.hasNext()) {
				writer.write(",\n    ");
			}
        }
        writer.write("]).\n\n\n\n");

        // Rename phases if necessary
        final Phase[] phases = converter.getPEA().getPhases();
        final Set<Phase> finalPhases = new HashSet<>(
                Arrays.asList(((PEATestAutomaton)converter.getPEA()).getFinalPhases()));
        if (rename) {
            int stateCounter = phases.length;
            for (int i = 0; i < phases.length; i++) {
                if (!finalPhases.contains(phases[i])) {
                    renameMap.put(phases[i].getName(), ARMCString.STATE_NAME + stateCounter);
                } else {
                    renameMap.put(phases[i].getName(), ARMCString.ERROR_LOC);
                }
                stateCounter--;
            }
        } else {// add phase prefix and rename bad states
            for (int i = 0; i < phases.length; i++) {
                if (!finalPhases.contains(phases[i])) {
                    renameMap.put(phases[i].getName(), ARMCString.LOC_PREFIX + phases[i].getName());
                } else {
                    renameMap.put(phases[i].getName(), ARMCString.ERROR_LOC);
                }
            }
        }
        
    }

    

    
    /**
     * Writes all initial constraints of the Transition Constraint System (generated
     * by PEA2TCSConverter) to the ARMC output.
     * 
     * @throws IOException
     *          thrown if writing of output file fails
     * @see PEA2TCSConverter
     */
    protected void writeInitialTransitions() throws IOException {
        TransitionConstraint initTrans = converter.getNextInitConstraint();
        while (initTrans != null) {

            writeTransitionPrefix(
                    ARMCString.INIT_LOC,
                    renameMap.get(initTrans.getInitLoc()));
            writeConstraintSorted(initTrans.getConstraint().prime());
            writeTransitionSuffix();
            
            initTrans = converter.getNextInitConstraint();
        }
    }
    
    
    /**
     * Writes all transitions (except for initial constraints) of the Transition
     * Constraint System (generated by PEA2TCSConverter) to the ARMC output.
     * 
     * @throws IOException
     *          thrown if writing of output file fails
     * @see PEA2TCSConverter
     */
    protected void writeTransitions() throws IOException {
        TransitionConstraint trans = converter.getNextTransitionConstraint();
        while (trans != null) {
            
            if(trans.getConstraint() == CDD.FALSE){
                trans = converter.getNextTransitionConstraint();
                continue;
            }
            writeTransitionPrefix(
                    renameMap.get(trans.getSource()),
                    renameMap.get(trans.getDest()));
            writeConstraintSorted(trans.getConstraint());
            writeTransitionSuffix();
            
            trans = converter.getNextTransitionConstraint();
        }
    }

    
    /**
     * The ARMC syntax requires that transition constraints are ordered by
     * update constraints and guard constraints (no primed variables). Hence,
     * this method takes a CDD constraint and writes all unprimed constraints to
     * the unPrimedWriter and all primed constraints to the primedWriter.
     * 
     * @param constraint
     *          Input constraint to be translated into ARMC syntax
     * @throws IOException
     *          thrown if writing of output file fails
     */
    protected void writeConstraintSorted(final CDD constraint) throws IOException {
        primedWriter = new StringWriter();
        unPrimedWriter = new StringWriter();
        firstPrimedConstraint = true;
        firstUnPrimedConstraint = true;
        /* writeConjunction is called with null as writer. By this, we enforce
         * that instead primedWriter and unPrimedWriter are filled with constraints,
         * which we then need to write to file manually.  */
        writeConjunction(constraint, null);

        primedWriter.close();
        unPrimedWriter.close();

        writer.write("[");
        writer.write(unPrimedWriter.toString());
        writer.write("],[");
        writer.write(primedWriter.toString());
        writer.write("]");
    }

    
    /**
     * Analogously to <code>writeConstraintSorted</code> this method writes a decision
     * to the writers unPrimedWriter and primedWriter depending on whether the
     * decision contains primed variables.
     * 
     * @param decision
     *          the decision to be written. The decision has to be different from null.
     * @param child
     *          the position of the decision in the belonging CDD
     *          (confer {@link de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision#toString(int)})
     * @throws IOException
     *          thrown if writing of output file fails
     */
    protected void writeDecisionSorted(final Decision decision, final int child) throws IOException {
        if(decision instanceof BooleanDecision
                && ((BooleanDecision)decision).getVar().contains(BooleanDecision.PRIME_SUFFIX)){

            if(firstPrimedConstraint) {
				firstPrimedConstraint = false;
			} else {
				primedWriter.write(", ");
			}
            
            writeDecision(decision, child, primedWriter);
        
//        }else if(decision instanceof ZDecision
//                && ((ZDecision)decision).getPredicate().contains(ZString.PRIME)){
//
//            if(firstPrimedConstraint)
//                firstPrimedConstraint = false;
//            else
//                primedWriter.write(", ");
//
//            writeDecision(decision, child, primedWriter);
        }else if  (decision instanceof RangeDecision
                && ((RangeDecision)decision).getVar().contains(BooleanDecision.PRIME_SUFFIX)){

            if(firstPrimedConstraint) {
				firstPrimedConstraint = false;
			} else {
				primedWriter.write(", ");
			}
        
            writeDecision(decision, child, primedWriter);

        }else{
            
            if(firstUnPrimedConstraint) {
				firstUnPrimedConstraint = false;
			} else {
				unPrimedWriter.write(", ");
			}
            
            writeDecision(decision, child, unPrimedWriter);
        }
    }


    /**
     * Outputs a common prefix of an ARMC transition. The prefix contains source
     * location and destination location which are given as parameters.
     * 
     * @param source
     *          the identifier of the transition's source location
     * @param dest
     *          the identifier of the transition's destination location
     * @throws IOException
     *          thrown if writing of output file fails
     */
    protected void writeTransitionPrefix(final String source, final String dest)
    throws IOException {
        writer.write("r(p(pc(" + source + "),data(" + varList + ")),");
        writer.write("p(pc(" + dest + "),data(" + primedVarList + ")), ");
    }
    

    /**
     * Writes the common suffix of ARMC transitions.
     * 
     * @throws IOException
     *          thrown if writing of output file fails
     */
    protected void writeTransitionSuffix() throws IOException {
        writer.write("," + (transCounter ++) + ").\n");
    }
    

    /* (non-Javadoc)
     * We do not use this method here to write the and delimiters (which is done
     * in pea.modelchecking.armc.ARMCWriter#writeDecisionSorted()).
     * Hence, this method shall only be called with writer == null.
     * 
     * @see pea.modelchecking.TCSWriter#writeAndDelimiter(java.io.Writer)
     */
    @Override
    protected void writeAndDelimiter(final Writer writer) throws IOException {
        assert writer == null;
    }


    /* (non-Javadoc)
     * 
     * If this method is called with
     *          writer == null
     * it first calls
     *          writeDecisionSorted(dec, i);
     * which computes the appropriate writer (unPrimedWriter or primedWriter)
     * and recalls this method with it.
     *
     * @see pea.modelchecking.TCSWriter#writeDecision(pea.Decision, int, java.io.Writer)
     */
    @Override
    protected void writeDecision(final Decision dec, final int i, final Writer writer)
            throws IOException {
        if(writer == null){
            writeDecisionSorted(dec, i);
            return;
        }
        
        if(dec instanceof RangeDecision){
            final String variable = ((RangeDecision)dec).getVar().replace(BooleanDecision.PRIME_SUFFIX,
                    ARMCString.ARMC_PRIME);
            writer.append(ARMCString.ARMC_US + variable);

            final int[] limits = ((RangeDecision)dec).getLimits();
            if (i == 0) {
                if ((limits[0] & 1) == 0) {
                    writer.append(" < ");
                } else {
                    writer.append(" =< ");
                }
                writer.append(Integer.toString(limits[0] / 2));
                return;
            }
            if (i == limits.length) {
                if ((limits[limits.length - 1] & 1) == 1) {
                    writer.append(" > ");
                } else {

                    writer.append(" >= ");
                }
                writer.append(Integer.toString(limits[limits.length - 1] / 2));
                return;
            }
            if (limits[i - 1] / 2 == limits[i] / 2) {
                writer.append(" > ");
                writer.append(Integer.toString(limits[i] / 2));
                return;
            }
            if ((limits[i - 1] & 1) == 1) {
                writer.append(" > ");
            } else {
                writer.append(" >= ");
            }
            writer.append(Integer.toString(limits[i - 1] / 2));
            writer.append(", ").append(ARMCString.ARMC_US + variable);


            if ((limits[i] & 1) == 0) {
                writer.append(" < ");
            } else {
                writer.append(" =< ");
            }
            writer.append(Integer.toString(limits[i] / 2));
            return;
        }
        if(i==0){
            if(dec instanceof RelationDecision){
                String toWrite = ((BooleanDecision)dec).getVar().replace(
                        RelationDecision.Operator.LEQ.toString(), ARMCString.LEQ);
                toWrite = toWrite.replace(RelationDecision.Operator.PRIME.toString(),
                        ARMCString.ARMC_PRIME);
                toWrite = toWrite.replaceAll("([a-zA-Z])(\\w*)", "_$1$2");
                writer.append(toWrite);
            } else if(dec instanceof BooleanDecision){
                String toWrite = ((BooleanDecision)dec).getVar().replace(
                        BooleanDecision.PRIME_SUFFIX,
                        ARMCString.ARMC_PRIME);
                toWrite = toWrite.replaceAll("([a-zA-Z])(\\w*)", "_$1$2");
                writer.append(toWrite);
            } else if(dec instanceof EventDecision){
                final String event = ((EventDecision)dec).getEvent();
                writer.append(event+" > "+event+"'");
//            } else if (dec instanceof ZDecision) {
//                String toWrite = ((ZDecision)dec).getPredicate();
//                toWrite = toWrite.replaceAll(ZString.PRIME, ARMCString.ARMC_PRIME);
//                toWrite = toWrite.replace(ZString.MINUS, ARMCString.MINUS);
//                toWrite = toWrite.replaceAll("([a-zA-Z])(\\w*)", "_$1$2");
//                if (!toWrite.contains(ZString.LEQ) && !toWrite.contains(ZString.GEQ)
//                        && !toWrite.contains("<") && !toWrite.contains(">")
//                        && !toWrite.contains("="))
//                    System.err.println(
//                            "warning: unknown operator in ZDecision: ("
//                            + toWrite + ")");
//                toWrite = toWrite.replace(ZString.LEQ, ARMCString.LEQ);
//                toWrite = toWrite.replace(ZString.GEQ, ARMCString.GEQ);
//                writer.append(toWrite);
            }
        }else{
            if(dec instanceof RelationDecision){
                String toWrite = ((RelationDecision)dec).toString(i);
                toWrite = toWrite.replaceAll("([a-zA-Z])(\\w*)", ARMCString.ARMC_US + "$1$2");
                toWrite = toWrite.replace(RelationDecision.Operator.PRIME.toString(),
                        ARMCString.ARMC_PRIME);
                if(toWrite.contains(RelationDecision.Operator.NEQ.toString())) {
					throw new RuntimeException("ARMC export: negated expressions not supported: " +
                            toWrite);
				}
                writer.append(toWrite);
            }else if(dec instanceof BooleanDecision){
                String toWrite = ((BooleanDecision)dec).toString(i);
                toWrite = toWrite.replaceAll("([a-zA-Z])(\\w*)", ARMCString.ARMC_US + "$1$2");
                toWrite = toWrite.replace(BooleanDecision.PRIME_SUFFIX, ARMCString.ARMC_PRIME);
                writer.append(toWrite);
            } else if(dec instanceof EventDecision){
                final String event = ((EventDecision)dec).getEvent();
                writer.append(event+" = "+event+"'");
//            } else if (dec instanceof ZDecision) {
//                String toWrite = ((ZDecision)dec).getPredicate();
//                toWrite = toWrite.replaceAll(ZString.PRIME, ARMCString.ARMC_PRIME);
//                toWrite = toWrite.replace(ZString.MINUS, "-");
//                toWrite = toWrite.replaceAll("([a-zA-Z])(\\w*)", "_$1$2");
//                if(toWrite.contains(ZString.GEQ)){
//                    writer.append(toWrite.replace(ZString.GEQ, "<"));
//                }else if(toWrite.contains(ZString.LEQ)){
//                    writer.append(toWrite.replace(ZString.LEQ, ">"));
//                } else if(toWrite.contains("<")){
//                    writer.append(toWrite.replace("<", ">="));
//                } else if(toWrite.contains(">")){
//                    writer.append(toWrite.replace(">", "=<"));
//                } else if(toWrite.contains("=")) {
//                    throw new RuntimeException("ARMC export: cannot negate '=' here;"
//                            + "term: " + toWrite);
//                } else {
//                    System.err.println(
//                            "warning: unknown operator in ZDecision: ("
//                            + toWrite + ")");
//                    writer.append(toWrite);
//                }
            }
        }

    }


    
}
