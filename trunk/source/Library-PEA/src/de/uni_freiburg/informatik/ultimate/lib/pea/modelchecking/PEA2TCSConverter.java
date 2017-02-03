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

package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.RelationDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;
import de.uni_freiburg.informatik.ultimate.lib.pea.ZDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.RelationDecision.Operator;
import net.sourceforge.czt.z.util.ZString;

/**
 * PEA2TCSConverter is a general converter class to convert Phase Event Automata (PEA) into Transition Constraint
 * Systems. This class only contains the construction of the transition constraints, independent of a concrete
 * output format. The output is produced by a TCSWriter object, writing the TransitionConstraints produced by
 * this class into an output file in a specific format.
 * 
 * @author jfaber
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata
 * @see TCSWriter
 * 
 */
public final class PEA2TCSConverter {

    
    /**
     * Type that is used for clocks and the len variable
     */
    public static final String REAL_TYPE = "\u211D";
    
    /**
     * 
     */
    public static final String LEN = "len";

    /**
     * TransitionConstraint is a simple container including
     * a transition constraint as CDD and the name of a source and a destination for 
     * the transition as String.
     *
     * @see de.uni_freiburg.informatik.ultimate.lib.pea.CDD
     * @author jfaber
     *
     */
    public static class TransitionConstraint {

        CDD constraint;
        String dest;
        String initLoc;
        String source;
        
        /**
         * Constructor to generate a TransitionConstraint as initial constraint.
         * @param constraint
         * @param initLoc
         */
        public TransitionConstraint(CDD constraint, String initLoc) {
            this.constraint = constraint;
            this.initLoc = initLoc;
        }

        /**
         * Constructor to generate a TransitionConstraint.
         * @param constraint
         * @param dest
         * @param source
         */
        public TransitionConstraint(CDD constraint, String source, String dest) {
            this.constraint = constraint;
            this.dest = dest;
            this.source = source;
        }

        /**
         * @return Returns the constraint.
         */
        public CDD getConstraint() {
            return constraint;
        }

        /**
         * @return Returns the dest.
         */
        public String getDest() {
            return dest;
        }

        /**
         * @return Returns the initLoc.
         */
        public String getInitLoc() {
            return initLoc;
        }

        /**
         * @return Returns the source.
         */
        public String getSource() {
            return source;
        }
        
    }
    
    private CDD clockConstraintForCurrentTrans;
    private final List<String> clocks;
    
    private Transition currentTransition;
    private Iterator<CDD> disjunctIterator;
    
    private CDD initClockConstraint;
    private Iterator<CDD> initDisjunctIterator;
    
    private int initPhaseCounter;
    private final Phase[] initPhases;
    private final PhaseEventAutomata pea;
    private int phaseCounter;
    private final Phase[] phases;
    private final TCSWriter tcsWriter;
    private Iterator<Transition> transitionIterator;
    private final Map<String,String> variables;
    private boolean useBooleanDecision = false;
    // len'>0
    private final CDD lenConstraint;
    private final Map<String, CDD> clockUpdatesReset;
    private final Map<String, CDD> clockUpdates;
    private final Map<String, CDD> stoppedClockUpdatesReset;
    private final Map<String, CDD> stoppedClockUpdates;

    private CDD globalInvariant = CDD.TRUE;
    
    
    /**
     * @param tcsWriter
     *          The TCSWriter instance that produces the output for the desired target syntax
     * @param pea
     *          The Phase Event Automaton to be transformed
     */
    public PEA2TCSConverter(TCSWriter tcsWriter, PhaseEventAutomata pea) {
        super();

        this.tcsWriter = tcsWriter;
        this.tcsWriter.setConverter(this);
        this.pea = pea;
        phases = pea.getPhases();
        initPhases = pea.getInit();
        clocks = pea.getClocks();
        variables = pea.getVariables();
        
        if (pea.getPhases().length == 0) {
            throw new RuntimeException(
                    "PEA with phase count = 0 is not allowed");
        }
        if (pea.getInit().length == 0) {
            throw new RuntimeException(
                    "PEA with initial phase count = 0 is not allowed");
        }

        globalInvariant = this.tcsWriter.processDeclarations(pea.getDeclarations(), variables);
        
        variables.put(LEN,REAL_TYPE);
        for (final String clock : clocks) {
            variables.put(clock,REAL_TYPE);
        }
        /* Add program counter to variable list */
        if(phases.length > 1) {
            variables.put("pc",ZString.NUM);
        }

        /* Calculate clock constraint for initial constraints*/
        initClockConstraint = 
        	useBooleanDecision ?
        	        RelationDecision.create("0", Operator.LESS, LEN) :
        			ZDecision.create("len>0");
        for (final String clock : clocks) {
            CDD cdd;
            if(useBooleanDecision){
                cdd = RelationDecision.create(clock, Operator.EQUALS, LEN);
            }else{
                cdd = ZDecision.create(clock + ZString.EQUALS + LEN);
            }
            initClockConstraint = initClockConstraint.and(cdd);
        }

        /* Calculate constraints which are used in nearly every transition */
        lenConstraint = useBooleanDecision ?
                RelationDecision.create("0", Operator.LESS, LEN + Operator.PRIME) :
                ZDecision.create(LEN + ZString.PRIME + ZString.GREATER + "0");
        
        /* Calculate clock update constraints for every clock */
        clockUpdatesReset = new HashMap<String,CDD>();
        clockUpdates= new HashMap<String,CDD>();
        stoppedClockUpdatesReset = new HashMap<String,CDD>();
        stoppedClockUpdates= new HashMap<String,CDD>();
        if(useBooleanDecision){
            for (final String clock : clocks) {
                clockUpdatesReset.put(clock, 
                        RelationDecision.create(clock 
                                + Operator.PRIME,  Operator.EQUALS,
                                LEN + Operator.PRIME));
                clockUpdates.put(clock,
                        RelationDecision.create(clock + Operator.PRIME,
                                Operator.EQUALS,
                                clock + Operator.PLUS
                                + LEN + Operator.PRIME));
                stoppedClockUpdatesReset.put(clock,
                        RelationDecision.create(clock + Operator.PRIME,
                                Operator.EQUALS,
                                "0"));
                stoppedClockUpdates.put(clock,
                        RelationDecision.create(clock + Operator.PRIME,
                                Operator.EQUALS,
                                clock));
            }                
        }else{
            for (final String clock : clocks) {
                clockUpdatesReset.put(clock,
                        ZDecision.create(clock + ZString.PRIME + ZString.EQUALS
                                + LEN + ZString.PRIME));
                clockUpdates.put(clock,
                        ZDecision.create(clock + ZString.PRIME + ZString.EQUALS
                                + clock + ZString.PLUS
                                + LEN + ZString.PRIME));
                stoppedClockUpdatesReset.put(clock,
                        ZDecision.create(clock + ZString.PRIME + ZString.EQUALS
                                + "0"));
                stoppedClockUpdates.put(clock,
                        ZDecision.create(clock + ZString.PRIME + ZString.EQUALS
                                + clock));
            }
        }        

    }

    
    /**
     *  Starts the conversion from PEA to TCS.
     */
    public void convert() {
        phaseCounter = -1;
        chooseNextTransition();
        initPhaseCounter = -1;
        chooseNextInitPhase();

        tcsWriter.write();
    }
    
    
    /**
     * This method is similar to chooseNextTransition. It selects the next initial phase depending on
     * the initPhaseCounter and calculates the initDisjunctIterator. Disjuncts result from the state and clock
     * invariants from the initial phase.
     * 
     * @return false if there is no next init phase, true otherwise.
     */
    private boolean chooseNextInitPhase() {
        if(++initPhaseCounter>=initPhases.length) {
			return false;
		}
        
        final CDD initStateInvariant = initPhases[initPhaseCounter].getStateInvariant().and(globalInvariant);
        final CDD initClockInvariant = initPhases[initPhaseCounter].getClockInvariant();

        final CDD[] initPhaseDisjuncts = initStateInvariant.and(initClockInvariant).toDNF();

        initDisjunctIterator = Arrays.asList(initPhaseDisjuncts).iterator();

        return true;
    }


    
    /**
     * Choose next transition from the phase event automaton belonging to this class.
     * It first checks whether there is a next transition for the currentPhase. Otherwise
     * it selects the next phase and a transition going out of this phase.
     * Additionally, chooseNextTransition recalculates the disjuncts list for the next transition,
     * i.e., a list of disjuncts resulting from the product of the disjuncts for the guard of the transition
     * and the invariants of the target location of this transition.
     * 
     * 
     * @return boolean 
     * 			Returns true if there is a next transition and false otherwise.
     */
    private boolean chooseNextTransition() {
        while(transitionIterator == null || !transitionIterator.hasNext()) {
            if(++phaseCounter < phases.length) {
                final List<Transition> transitionsForPhase = phases[phaseCounter].getTransitions();
                transitionIterator = transitionsForPhase.iterator();
            }else {
                return false;
            }
        }
        currentTransition = transitionIterator.next();

        final CDD guard = currentTransition.getGuard();
        if(guard == CDD.FALSE){
            return chooseNextTransition();
        }

        final CDD[] transitionDisjuncts = guard.toDNF();
        
        final CDD destStateInvariant = currentTransition.getDest().getStateInvariant().and(globalInvariant);
        final CDD destClockInvariant = currentTransition.getDest().getClockInvariant();
        final CDD[] invariantDisjuncts = destStateInvariant.and(destClockInvariant).toDNF();
        
        final ArrayList<CDD> disjuncts = new ArrayList<CDD>();
        for (int i = 0; i < transitionDisjuncts.length; i++) {
            final CDD transDisj = transitionDisjuncts[i];
            for (int j = 0; j < invariantDisjuncts.length; j++) {
                final CDD invDisj = invariantDisjuncts[j];
                disjuncts.add(transDisj.and(invDisj.prime()));
            }
        } 
        disjunctIterator = disjuncts.iterator();

        // len'>0
        CDD constraint = lenConstraint;
        
        /* create Decision for updating clock values */
        final Set<String> resets = 
            new HashSet<String>(Arrays.asList(currentTransition.getResets()));
        for (final String clock : clocks) {
            CDD cdd;
            if(resets.contains(clock)){
                if(currentTransition.getDest().isStopped(clock)){
                    cdd = stoppedClockUpdatesReset.get(clock);
                }else{
                    cdd = clockUpdatesReset.get(clock);
                }
            }else{
                if(currentTransition.getDest().isStopped(clock)){
                    cdd = stoppedClockUpdates.get(clock);
                }else{
                    cdd = clockUpdates.get(clock);
                }
            }
            constraint = constraint.and(cdd);
        }
        
        clockConstraintForCurrentTrans = constraint;

        return true;
    }
        
 
    
    
    
    
    /**
     * Return the list of local declarations belonging to the current
     * PEA.
     * @return
     *          declarations as list of strings
     */
    public List<String> getDeclarations(){
        return pea.getDeclarations();
    }

    
    /**
     * Returns the name of the current PEA.
     * @return the name as String
     */
    public String getName() {
        return pea.getName();
    }

    /**
     * Similar to getNextTransition(). This method iterates over the constraints (state and clock invariants) of
     * all inital phases of the input PEA and it returns the next disjunct representing the next initial constraint. 
     * 
     * @return A TransitionConstraint representing a initial constraint. Returns null if there is no next init
     * constraint.
     */
    public TransitionConstraint getNextInitConstraint() {
       CDD initDisjunct;
        
        if(initDisjunctIterator.hasNext()) {
            initDisjunct = initDisjunctIterator.next();
        }else {
            /* chooseNextInitPhase() reinitialises initDisjunctIterator
               for the next initial phase if possible */
            if(!chooseNextInitPhase()){
                return null;
            }
            initDisjunct = initDisjunctIterator.next();
        }

        final CDD constraint = initDisjunct.and(initClockConstraint);

        final String initLoc = initPhases[initPhaseCounter].getName();

        return new TransitionConstraint(constraint, initLoc);
    }

    /**
     * Generates the next transition constraint for the current phase event automaton. 
     * 
     * This method iterates over all disjuncts from transitions and invariants of the PEA and 
     * combines a disjunct for a transition and a disjunct from the invariant constraint for the destination of 
     * the transition to a Transition constraint. 
     * 
     * @return a TransitionConstraint object for the next transition.
     */
    public TransitionConstraint getNextTransitionConstraint() {
        CDD disjunct;
        
        if(disjunctIterator.hasNext()) {
            disjunct = disjunctIterator.next();
        }else {
            if(!chooseNextTransition()){
                return null;
            }
            if(!disjunctIterator.hasNext()) {
				System.out.println();
			}
            disjunct = disjunctIterator.next();
        }

        final CDD constraint = disjunct.and(clockConstraintForCurrentTrans);

        final String source = currentTransition.getSrc().getName();
        final String dest = currentTransition.getDest().getName();

        return new TransitionConstraint(constraint, source, dest);
    }
    
    /**
     * @return Returns the variables.
     */
    public Map<String,String> getVariables() {
        return variables;
    }

    /**
     * @return Returns the PEA processed by this class.
     */
    public PhaseEventAutomata getPEA() {
        return pea;
    }

    /**
     * Set the useBooleanDecision flag indicating that a BooleanDecision is used 
     * for all newly generated decisions.
     */
    public void useBooleanDecision() {
        useBooleanDecision = true;
    }

    /**
     * Set the useBooleanDecision flag indicating that a BooleanDecision is used 
     * for all newly generated decisions.
     */
    public void useZDecision() {
        useBooleanDecision = false;
    }


}
