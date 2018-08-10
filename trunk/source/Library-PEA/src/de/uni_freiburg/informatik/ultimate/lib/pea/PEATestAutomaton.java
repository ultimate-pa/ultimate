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
package de.uni_freiburg.informatik.ultimate.lib.pea;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.lib.pea.util.SimpleSet;

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
    public PEATestAutomaton(final String name, final Phase[] phases, final Phase[] init,
            final List<String> clocks) {
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
    public PEATestAutomaton(final String name, final Phase[] phases, final Phase[] init,
            final List<String> clocks, final Phase[] finals) {
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
    public PEATestAutomaton(final String name, final Phase[] phases, final Phase[] init) {
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
    public PEATestAutomaton(final String name, final Phase[] phases, final Phase[] init,
            final List<String> clocks, final Map<String, String> variables,
            final List<String> declarations, final Phase[] finalPhases) {
        super(name, phases, init, clocks, variables, declarations);
        this.finalPhases = finalPhases != null ? finalPhases : new Phase[0];
    }

    public PEATestAutomaton(final PhaseEventAutomata automata) {
        this(automata.mName, automata.mPhases, automata.mInit, automata.mClocks,
                automata.mVariables, automata.mDeclarations, new Phase[0]);
    }

    
    
    
    
    /**
     * Computes the parallel product of a test automaton and an arbitrary PEA. If this
     * PEA is also a test automaton then the new final states are given by tuples of finals
     * states of both components. Otherwise this PEA is not a test automaton and the new
     * final states are given by the product of final states of the test automaton and
     * normal states of the PEA.
     */
    @Override
	public PEATestAutomaton parallel(final PhaseEventAutomata b) {
        final List<Phase> newInit = new ArrayList<>();
        final List<Phase> newFinal = new ArrayList<>();
        final TreeSet<Phase> oldFinal = getFinalPhases() == null ? null :
                                new TreeSet<>(Arrays.asList(getFinalPhases()));
        TreeSet<Phase> bOldFinal = null;
        
        final TreeMap<String,Phase> newPhases = new TreeMap<>();
        final boolean bIsTestAutomaton = (b instanceof PEATestAutomaton);
        if(bIsTestAutomaton){
            bOldFinal = new TreeSet<>(Arrays.asList(((PEATestAutomaton)b).getFinalPhases()));
        }
        
               
        
        class TodoEntry {
            Phase p1,p2,p;
            TodoEntry(final Phase p1, final Phase p2, final Phase p) {
            this.p1 = p1;
            this.p2 = p2;
            this.p = p;
            }
        }
        
        final List<TodoEntry> todo = new LinkedList<>();

        for (int i = 0; i < getInit().length; i++) {
            for (int j = 0; j < b.getInit().length; j++) {
            final CDD sinv = getInit()[i].stateInv.and(b.getInit()[j].stateInv);
            if (sinv != CDD.FALSE) {
                final CDD cinv = getInit()[i].clockInv.and(b.getInit()[j].clockInv);
                final Phase p = new Phase(getInit()[i].getName()+TIMES+b.getInit()[j].getName(),
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

        while (!todo.isEmpty()) {
            final TodoEntry entry = todo.remove(0);
            final Iterator<Transition> i = entry.p1.transitions.iterator();
            while (i.hasNext()) {
            final Transition t1 = i.next();
            final Iterator<Transition> j = entry.p2.transitions.iterator();
            while (j.hasNext()) {
                final Transition t2 = j.next();

                final CDD guard = t1.guard.and(t2.guard);
                if (guard == CDD.FALSE) {
					continue;
				}
                final CDD sinv = t1.dest.stateInv.and(t2.dest.stateInv);
                if (sinv == CDD.FALSE) {
					continue;
				}
                final CDD cinv = t1.dest.clockInv.and(t2.dest.clockInv);
                final String[] resets
                = new String[t1.resets.length + t2.resets.length];
                System.arraycopy(t1.resets, 0, resets, 0,
                         t1.resets.length);
                System.arraycopy(t2.resets, 0, resets, t1.resets.length,
                         t2.resets.length);
                
		final Set<String> stoppedClocks =
		    new SimpleSet<>(t1.dest.stoppedClocks.size()+
					  t2.dest.stoppedClocks.size());
		stoppedClocks.addAll(t1.dest.stoppedClocks);
		stoppedClocks.addAll(t2.dest.stoppedClocks);
		    
                final String newname = t1.dest.getName()+TIMES+t2.dest.getName();
                Phase p = newPhases.get(newname);

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
    

        final Phase[] allPhases = newPhases.values().toArray(new Phase[newPhases.size()]);
        final Phase[] initPhases = newInit.toArray(new Phase[newInit.size()]);
        final Phase[] finalPhases = newFinal.toArray(new Phase[newFinal.size()]);

        
        final List<String> newClocks = mergeClockLists(b);
        
        final Map<String, String> newVariables = mergeVariableLists(b);
        
        final List<String> newDeclarations = mergeDeclarationLists(b);
        
        return new PEATestAutomaton(mName + TIMES + b.mName,
                          allPhases, initPhases,
                          newClocks, newVariables, newDeclarations,
                          finalPhases);
        }

    public Phase[] getFinalPhases() {
        return finalPhases;
    }

    public void setFinalPhases(final Phase[] finalPhases) {
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
        final Map<Phase, List<Transition>> incomingTrans = new HashMap<>();
        for (final Phase phase : mPhases) {
            incomingTrans.put(phase, new ArrayList<Transition>());
        }
        for (final Phase phase : mPhases) {
            for (final Transition transition : phase.getTransitions()) {
                incomingTrans.get(transition.dest).add(transition);
            }
        }
        
        // collect reachable transitions
        final HashSet<Phase> reachablePhases = new HashSet<>();
        final HashSet<Transition> reachableTrans = new HashSet<>();
        List<Phase> unworked = Arrays.asList(getFinalPhases());
        while(!unworked.isEmpty()){
            final List<Phase> temp = new ArrayList<>();
            for (final Phase phase : unworked) {
                reachablePhases.add(phase);
                for (final Transition trans : incomingTrans.get(phase)){
                    reachableTrans.add(trans);
                    if(!reachablePhases.contains(trans.src) && !unworked.contains(trans.src)) {
						temp.add(trans.src);
					}
                }
            }
            unworked = temp;
        }
        
        // check if there are unreachable phases
        if(reachablePhases.size() == mPhases.length) {
			return this;
		}
        
        // a new phase sinkPhase shall replace the unreachable phases
        final List<Phase> newPhases = new ArrayList<>();
        final ArrayList<Phase> newInit = new ArrayList<>();
        final Phase sinkPhase = new Phase("sink");
        newPhases.add(sinkPhase);
        sinkPhase.addTransition(sinkPhase, CDD.TRUE, new String[0]);

        // check if one of the unreachable phases is an inital phase
        boolean initUnreachable = false;
        for (final Phase initPhase : mInit){
            if(reachablePhases.contains(initPhase)) {
				newInit.add(initPhase);
			} else {
				initUnreachable = true;
			}
        }
        if(initUnreachable) {
			newInit.add(sinkPhase);
		}
                        

        // rebuild PEATestAutomaton
        for (final Phase phase : mPhases) {
            if(reachablePhases.contains(phase)){
                newPhases.add(phase);
                final List<Transition> removeList = new ArrayList<>();
                for (final Transition trans: phase.transitions) {
                    if(!reachableTrans.contains(trans)){
                        removeList.add(trans);
                    }
                }
                for (final Transition trans: removeList) {
                    phase.addTransition(sinkPhase,trans.getGuard(),trans.getResets());
                    phase.getTransitions().remove(trans);
                }
                
            }else{
                newInit.remove(phase);
            }
        }
        
        return new PEATestAutomaton(mName, newPhases.toArray(new Phase[newPhases.size()]),
                newInit.toArray(new Phase[newInit.size()]),mClocks,
                mVariables, mDeclarations, finalPhases);
    }
    
    @Override
	public void dump() {
        System.err.println("automata "+mName+ " { ");
        System.err.print("clocks: ");
        final Iterator<String> clockIter = mClocks.iterator();
        while (clockIter.hasNext()) {
            final String actClock = clockIter.next();
            System.err.print(actClock);
            if(clockIter.hasNext()) {
                System.err.print(", ");
            }
        }
        System.err.println("");
        System.err.print("  init { ");
        String delim = "";
        for (int i = 0; i < mInit.length; i++) {
            System.err.print(delim + mInit[i]);
            delim = ", ";
        }
        System.err.println(" }");
        for (int i = 0; i < mPhases.length; i++) {
            mPhases[i].dump();
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
