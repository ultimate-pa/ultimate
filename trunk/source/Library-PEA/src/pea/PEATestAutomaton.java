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
package pea;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Set;
import pea.util.SimpleSet;

import pea.CDD;
import pea.Phase;
import pea.PhaseEventAutomata;
import pea.Transition;

/**
 * This class implements a PEA test automaton that is a Phase Event Automaton with
 * final (or bad) locations.
 * 
 * @author Johannes Faber
 */
public class PEATestAutomaton extends PhaseEventAutomata {

    protected Phase[] finalPhases;
    
    /**
     * @param name
     * @param phases
     * @param init
     * @param clocks
     */
    public PEATestAutomaton(String name, Phase[] phases, Phase[] init,
            List<String> clocks) {
        this(name, phases, init, clocks, new Phase[0]);
    }

    /**
     * Field constructor.
     * 
     * @param name
     * @param phases
     * @param init
     * @param clocks
     */
    public PEATestAutomaton(String name, Phase[] phases, Phase[] init,
            List<String> clocks, Phase[] finals) {
        this(name, phases, init, clocks, null, null, finals);
    }

    
    /**
     * Field constructor.
     * Fields that are not set remain null.
     *      
     * @param name
     * @param phases
     * @param init
     */
    public PEATestAutomaton(String name, Phase[] phases, Phase[] init) {
        super(name, phases, init);
        finalPhases = new Phase[0];
    }

    /**
     * Constructor initializing all fields.
     * 
     * @param name
     * @param phases
     * @param init
     * @param clocks
     * @param variables
     * @param declarations
     * @param finalPhases
     *          if finalPhases is null then a new Phase array
     *          is generated for the final phases
     */
    public PEATestAutomaton(String name, Phase[] phases, Phase[] init,
            List<String> clocks, Map<String, String> variables,
            List<String> declarations, Phase[] finalPhases) {
        super(name, phases, init, clocks, variables, declarations);
        this.finalPhases = finalPhases != null ? finalPhases : new Phase[0];
    }

    public PEATestAutomaton(PhaseEventAutomata automata) {
        this(automata.name, automata.phases, automata.init, automata.clocks, 
                automata.variables, automata.declarations, new Phase[0]);
    }

    
    
    
    
    /**
     * Computes the parallel product of a test automaton and an arbitrary PEA. If this
     * PEA is also a test automaton then the new final states are given by tuples of finals
     * states of both components. Otherwise this PEA is not a test automaton and the new
     * final states are given by the product of final states of the test automaton and
     * normal states of the PEA.
     */
    public PEATestAutomaton parallel(PhaseEventAutomata b) {
        List<Phase> newInit = new ArrayList<Phase>();
        List<Phase> newFinal = new ArrayList<Phase>();
        TreeSet<Phase> oldFinal = this.getFinalPhases() == null ? null :
                                new TreeSet<Phase>(Arrays.asList(this.getFinalPhases()));
        TreeSet<Phase> bOldFinal = null;
        
        TreeMap<String,Phase> newPhases = new TreeMap<String,Phase>();
        boolean bIsTestAutomaton = (b instanceof PEATestAutomaton);
        if(bIsTestAutomaton){
            bOldFinal = new TreeSet<Phase>(Arrays.asList(((PEATestAutomaton)b).getFinalPhases()));
        }
        
               
        
        class TodoEntry {
            Phase p1,p2,p;
            TodoEntry(Phase p1, Phase p2, Phase p) {
            this.p1 = p1;
            this.p2 = p2;
            this.p = p;
            }
        }
        
        List<TodoEntry> todo = new LinkedList<TodoEntry>();

        for (int i = 0; i < getInit().length; i++) {
            for (int j = 0; j < b.getInit().length; j++) {
            CDD sinv = getInit()[i].stateInv.and(b.getInit()[j].stateInv);
            if (sinv != CDD.FALSE) {
                CDD cinv = getInit()[i].clockInv.and(b.getInit()[j].clockInv);
                Phase p = new Phase(getInit()[i].getName()+TIMES+b.getInit()[j].getName(),
                        sinv, cinv);
                if(bIsTestAutomaton &&
                        oldFinal.contains(getInit()[i]) &&
                        bOldFinal.contains(b.getInit()[j])){
                         newFinal.add(p);
                }else if(!bIsTestAutomaton && oldFinal != null && oldFinal.contains(getInit()[i])){
                         newFinal.add(p);
                }
                newInit.add(p);
                newPhases.put(p.getName(), p);
                todo.add(new TodoEntry(getInit()[i],b.getInit()[j],p));       
            }
            }
        }

        while (todo.size() > 0) {
            TodoEntry entry = (TodoEntry) todo.remove(0);
            Iterator i = entry.p1.transitions.iterator();
            while (i.hasNext()) {
            Transition t1 = (Transition) i.next();
            Iterator j = entry.p2.transitions.iterator();
            while (j.hasNext()) {
                Transition t2 = (Transition) j.next();

                CDD guard = t1.guard.and(t2.guard);
                if (guard == CDD.FALSE)
                continue;
                CDD sinv = t1.dest.stateInv.and(t2.dest.stateInv);
                if (sinv == CDD.FALSE)
                continue;
                CDD cinv = t1.dest.clockInv.and(t2.dest.clockInv);
                String[] resets
                = new String[t1.resets.length + t2.resets.length];
                System.arraycopy(t1.resets, 0, resets, 0, 
                         t1.resets.length);
                System.arraycopy(t2.resets, 0, resets, t1.resets.length, 
                         t2.resets.length);
                
		Set<String> stoppedClocks = 
		    new SimpleSet<String>(t1.dest.stoppedClocks.size()+
					  t2.dest.stoppedClocks.size());
		stoppedClocks.addAll(t1.dest.stoppedClocks);
		stoppedClocks.addAll(t2.dest.stoppedClocks);
		    
                String newname = t1.dest.getName()+TIMES+t2.dest.getName();
                Phase p = (Phase) newPhases.get(newname);

                if (p == null) {
		    p = new Phase(newname, sinv, cinv, stoppedClocks);
                newPhases.put(newname, p);
                todo.add(new TodoEntry(t1.dest, t2.dest, p));
                if(bIsTestAutomaton && oldFinal != null && bOldFinal != null &&
                   oldFinal.contains(t1.dest) &&
                   bOldFinal.contains(t2.dest)){
                    newFinal.add(p);
                }else if(!bIsTestAutomaton && oldFinal != null && oldFinal.contains(t1.dest)){
                    newFinal.add(p);
                }

                }
                entry.p.addTransition(p, guard, resets);
            }
            }
        }
    

        Phase[] allPhases = (Phase[]) newPhases.values().toArray(new Phase[0]);
        Phase[] initPhases = (Phase[]) newInit.toArray(new Phase[0]);
        Phase[] finalPhases = (Phase[]) newFinal.toArray(new Phase[0]);

        
        List<String> newClocks = mergeClockLists(b);
        
        Map<String, String> newVariables = mergeVariableLists(b);
        
        List<String> newDeclarations = mergeDeclarationLists(b);
        
        return new PEATestAutomaton(name + TIMES + b.name, 
                          allPhases, initPhases, 
                          newClocks, newVariables, newDeclarations,
                          finalPhases);
        }

    public Phase[] getFinalPhases() {
        return finalPhases;
    }

    public void setFinalPhases(Phase[] finalPhases) {
        this.finalPhases = finalPhases;
    }
    
    /**
     * Computes locations that are backward reachable from final locations and
     * replaces all locations that are not reachable with one new location. Note that
     * we do not simple remove unreachable state to avoid deadlock introduction in
     * the parallel composition of test automata and model.  
     * @return the simplified test automaton 
     */
    public PEATestAutomaton removeUnreachableLocations(){
        // building up map for more efficient access to incoming transitions
        Map<Phase, List<Transition>> incomingTrans = new HashMap<Phase, List<Transition>>();
        for (Phase phase : phases) {
            incomingTrans.put(phase, new ArrayList<Transition>());
        }
        for (Phase phase : phases) {
            for (Transition transition : phase.getTransitions()) {
                incomingTrans.get(transition.dest).add(transition);
            }
        }
        
        // collect reachable transitions
        HashSet<Phase> reachablePhases = new HashSet<Phase>();
        HashSet<Transition> reachableTrans = new HashSet<Transition>();
        List<Phase> unworked = Arrays.asList(getFinalPhases());
        while(!unworked.isEmpty()){
            List<Phase> temp = new ArrayList<Phase>();
            for (Phase phase : unworked) {
                reachablePhases.add(phase);
                for (Transition trans : incomingTrans.get(phase)){
                    reachableTrans.add(trans);
                    if(!reachablePhases.contains(trans.src) && !unworked.contains(trans.src))
                        temp.add(trans.src);
                }
            }
            unworked = temp;
        }
        
        // check if there are unreachable phases
        if(reachablePhases.size() == this.phases.length)
            return this;
        
        // a new phase sinkPhase shall replace the unreachable phases
        List<Phase> newPhases = new ArrayList<Phase>();
        ArrayList<Phase> newInit = new ArrayList<Phase>();
        Phase sinkPhase = new Phase("sink");
        newPhases.add(sinkPhase);
        sinkPhase.addTransition(sinkPhase, CDD.TRUE, new String[0]);

        // check if one of the unreachable phases is an inital phase
        boolean initUnreachable = false;
        for (Phase initPhase : init){
            if(reachablePhases.contains(initPhase))
                newInit.add(initPhase);
            else
                initUnreachable = true;
        }
        if(initUnreachable)
            newInit.add(sinkPhase);
                        

        // rebuild PEATestAutomaton
        for (Phase phase : this.phases) {
            if(reachablePhases.contains(phase)){
                newPhases.add(phase);
                List<Transition> removeList = new ArrayList<Transition>();
                for (Transition trans: phase.transitions) {
                    if(!reachableTrans.contains(trans)){
                        removeList.add(trans);
                    }
                }
                for (Transition trans: removeList) {
                    phase.addTransition(sinkPhase,trans.getGuard(),trans.getResets());
                    phase.getTransitions().remove(trans);
                }
                
            }else{
                newInit.remove(phase);
            }
        }
        
        return new PEATestAutomaton(this.name,newPhases.toArray(new Phase[0]),
                newInit.toArray(new Phase[0]),this.clocks, 
                this.variables, this.declarations, this.finalPhases);
    }
    
    public void dump() {
        System.err.println("automata "+name+ " { ");
        System.err.print("clocks: ");
        Iterator clockIter = this.clocks.iterator();
        while (clockIter.hasNext()) {
            String actClock = (String) clockIter.next();
            System.err.print(actClock);
            if(clockIter.hasNext()) {
                System.err.print(", ");
            }
        }
        System.err.println("");
        System.err.print("  init { ");
        String delim = "";
        for (int i = 0; i < init.length; i++) {
            System.err.print(delim + init[i]);
            delim = ", ";
        }
        System.err.println(" }");
        for (int i = 0; i < phases.length; i++) {
            phases[i].dump();
        }
        System.err.println("}");
        
        System.err.print("  final { ");
        delim = "";
        if(finalPhases != null){
            for (int i = 0; i < finalPhases.length; i++) {
                System.err.print(delim + finalPhases[i]);
                delim = ", ";
            }
        }
        System.err.println("}");
    }

}
