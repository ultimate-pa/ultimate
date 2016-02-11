/*
 * Copyright (C) 2016 Jens Stimpfle <stimpflj@informatik.uni-freiburg.de>

 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import org.apache.log4j.Logger;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;

/**
 * Convert a <code>INestedWordAutomaton</code> to a <code>NiceNWA</code>
 * structure. Using the <code>constructMerge()</code> method,
 * a new smaller automaton can be made later, given a
 * <code>NestedWordAutomaton</code> later, given a <code>StateFactory</code>
 * and a <code>NiceClasses</code> structure.
 * 
 * <p>This can't be more than best effort unless the exact type of the input
 * NWA is known and/or the interface documentation is improved (what methods
 * are (intended to be) non-destructive, what invariants are there, what is
 * the complexity of the operations?...)
 * 
 * @author stimpflj
 */
public class NiceConvert<LETTER, STATE> {
	private Logger logger;
	private IUltimateServiceProvider services;
	private StateFactory<STATE> factory;
	
	// LETTERs are shared between old (input) and new (output) automaton
	private Set<LETTER> iAlphabet;
	private Set<LETTER> cAlphabet;
	private Set<LETTER> rAlphabet;
	
	// LETTERs <-> Integers bijection
	private HashMap<LETTER, Integer> iSymIndex;
	private HashMap<LETTER, Integer> cSymIndex;
	private HashMap<LETTER, Integer> rSymIndex;
	private ArrayList<LETTER> iSym;
	private ArrayList<LETTER> cSym;
	private ArrayList<LETTER> rSym;
	
	// STATEs are *not* shared between old and new automaton
	private Set<STATE> oldStates;
	private Set<STATE> oldInitialStates;
	private Collection<STATE> oldFinalStates;
	
	// STATEs <-> Integers bijection
	private HashMap<STATE, Integer> oldStateIndex;
	private ArrayList<STATE> oldState;
	
	private NiceNWA converted;
	
	/**
	 * @return NiceNWA generated from input automaton. Don't modify this
	 *         automaton since its state is need for converting back to
	 *         a NestedWordAutomaton.
	 *         If you need to make modifications, make a copy with .clone()
	 *         first.
	 */
	public NiceNWA getNiceNWA() { return converted; }
	
	public NiceConvert(Logger logger,
			IUltimateServiceProvider services,
			INestedWordAutomaton<LETTER, STATE> automaton,
			StateFactory<STATE> factory) {
		this.logger = logger;
		this.services = services;
		this.factory = factory;

		oldStates = automaton.getStates();
		oldInitialStates = automaton.getInitialStates();
		oldFinalStates = automaton.getFinalStates();
		
		iAlphabet = automaton.getInternalAlphabet();
		cAlphabet = automaton.getCallAlphabet();
		rAlphabet = automaton.getReturnAlphabet();

		oldStateIndex = new HashMap<STATE, Integer>();		
		oldState = new ArrayList<STATE>();

		iSymIndex = new HashMap<LETTER, Integer>();
		cSymIndex = new HashMap<LETTER, Integer>();
		rSymIndex = new HashMap<LETTER, Integer>();
		
		iSym = new ArrayList<LETTER>();
		cSym = new ArrayList<LETTER>();
		rSym = new ArrayList<LETTER>();
		
		for (STATE st : oldStates) {
			assert !oldStateIndex.containsKey(st);
			int idx = oldState.size();
			oldStateIndex.put(st, idx);
			oldState.add(st);
		}
		
		for (LETTER isym : iAlphabet) {
			assert !iSymIndex.containsKey(isym);
			int idx = iSym.size();
			iSymIndex.put(isym, idx);
			iSym.add(isym);
		}
		
		for (LETTER csym : cAlphabet) {
			assert !cSymIndex.containsKey(csym);
			int idx = cSym.size();
			cSymIndex.put(csym, idx);
			cSym.add(csym);
		}
		
		for (LETTER rsym : rAlphabet) {
			assert !rSymIndex.containsKey(rsym);
			int idx = rSym.size();
			rSymIndex.put(rsym, idx);
			rSym.add(rsym);
		}

		int numStates = oldState.size();
		int numISyms = iSym.size();
		int numCSyms = cSym.size();
		int numRSyms = rSym.size();
		
		boolean[] isInitial = new boolean[numStates];
		boolean[] isFinal = new boolean[numStates];
		
		for (int i = 0; i < numStates; i++) isInitial[i] = oldInitialStates.contains(oldState.get(i));
		for (int i = 0; i < numStates; i++) isFinal[i] = oldFinalStates.contains(oldState.get(i));
		
		ArrayList<NiceITrans> iTrans = new ArrayList<NiceITrans>();
		ArrayList<NiceCTrans> cTrans = new ArrayList<NiceCTrans>();
		ArrayList<NiceRTrans> rTrans = new ArrayList<NiceRTrans>();
		
		for (int i = 0; i < numStates; i++) {
			STATE st = oldState.get(i);
			for (OutgoingInternalTransition<LETTER, STATE> x : automaton.internalSuccessors(st)) iTrans.add(new NiceITrans(i, iSymIndex.get(x.getLetter()), oldStateIndex.get(x.getSucc())));
			for (OutgoingCallTransition<LETTER, STATE>     x : automaton.callSuccessors(st))     cTrans.add(new NiceCTrans(i, cSymIndex.get(x.getLetter()), oldStateIndex.get(x.getSucc())));
			for (OutgoingReturnTransition<LETTER, STATE>   x : automaton.returnSuccessors(st))   rTrans.add(new NiceRTrans(i, rSymIndex.get(x.getLetter()), oldStateIndex.get(x.getHierPred()), oldStateIndex.get(x.getSucc())));
		}

		this.converted = new NiceNWA();
		
		converted.numStates = numStates;
		converted.numISyms = numISyms;
		converted.numCSyms = numCSyms;
		converted.numRSyms = numRSyms;
		converted.isInitial = isInitial;
		converted.isFinal = isFinal;
		converted.iTrans = iTrans.toArray(new NiceITrans[iTrans.size()]);
		converted.cTrans = cTrans.toArray(new NiceCTrans[cTrans.size()]);
		converted.rTrans = rTrans.toArray(new NiceRTrans[rTrans.size()]);
	}
	
	/**
	 * @param eqCls A (consistent) NiceClasses which represents the
	 *        minimized automaton. The number of old states in eqCls (i.e.,
	 *        eqCls.classOf.length) must be consistent with the old automaton
	 *        stored in this NiceConvert instance.
	 * @return A NestedWordAutomaton constructed from eqCls.
	 */
	public NestedWordAutomaton<LETTER, STATE> constructMerged(NiceClasses eqCls) {
		assert(eqCls.classOf.length == oldState.size());
		int[] cls = eqCls.classOf;
		int numNewStates = eqCls.numClasses;
		
		HashSet<NiceITrans> newITrans = new HashSet<NiceITrans>();
		HashSet<NiceCTrans> newCTrans = new HashSet<NiceCTrans>();
		HashSet<NiceRTrans> newRTrans = new HashSet<NiceRTrans>();
		
		for (NiceITrans x : converted.iTrans) newITrans.add(new NiceITrans(cls[x.src], x.sym, cls[x.dst]));
		for (NiceCTrans x : converted.cTrans) newCTrans.add(new NiceCTrans(cls[x.src], x.sym, cls[x.dst]));
		for (NiceRTrans x : converted.rTrans) newRTrans.add(new NiceRTrans(cls[x.src], cls[x.sym], cls[x.top], cls[x.dst]));
		
		ArrayList<ArrayList<STATE>> stateClass = new ArrayList<ArrayList<STATE>>();

		for (int i = 0; i < numNewStates; i++)
			stateClass.add(new ArrayList<STATE>());
		
		for (int i = 0; i < oldState.size(); i++)
			stateClass.get(cls[i]).add(oldState.get(i));
		
		for (int i = 0; i < numNewStates; i++)
			assert !stateClass.get(i).isEmpty();
		
		ArrayList<STATE> newState = new ArrayList<STATE>();
		
		for (int i = 0; i < numNewStates; i++)
			newState.add(factory.minimize(stateClass.get(i)));
		
		NestedWordAutomaton<LETTER, STATE> nwa = new NestedWordAutomaton<LETTER, STATE>(services, iAlphabet, cAlphabet, rAlphabet, factory);
		
		for (int i = 0; i < numNewStates; i++) {
			STATE someOldState = stateClass.get(i).get(0);
			nwa.addState(oldInitialStates.contains(someOldState),
						 oldFinalStates.contains(someOldState), newState.get(i));
		}
		for (NiceITrans x : newITrans) nwa.addInternalTransition(newState.get(x.src), iSym.get(x.sym), newState.get(x.dst));
		for (NiceCTrans x : newCTrans) nwa.addCallTransition    (newState.get(x.src), cSym.get(x.sym), newState.get(x.dst));
		for (NiceRTrans x : newRTrans) nwa.addReturnTransition  (newState.get(x.src), newState.get(x.top), rSym.get(x.sym), newState.get(x.dst));		

		return nwa;
	}
}
