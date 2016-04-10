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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.maxsat;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;

/**
 * Convert a <code>INestedWordAutomaton</code> to a <code>NWA</code> structure.
 * Using the <code>constructMerged()</code> method, a smaller equivalent
 * <code>NestedWordAutomaton</code> can be made later given a
 * <code>Partition</code> structure.
 *
 * @author stimpflj
 */
final class Converter<LETTER, STATE> {

	private AutomataLibraryServices services;
	private StateFactory<STATE> factory;
	private INestedWordAutomaton<LETTER, STATE> automaton;

	/* LETTERs are shared between old (input) and new (output) automaton
	 */
	private Set<LETTER> iAlphabet;
	private Set<LETTER> cAlphabet;
	private Set<LETTER> rAlphabet;

	/* LETTERs <-> Integers bijection
	 */
	private HashMap<LETTER, Integer> iSymIndex;
	private HashMap<LETTER, Integer> cSymIndex;
	private HashMap<LETTER, Integer> rSymIndex;
	private ArrayList<LETTER> iSym;
	private ArrayList<LETTER> cSym;
	private ArrayList<LETTER> rSym;

	/* STATEs are *not* shared between old and new automaton
	 */
	private Set<STATE> oldStates;
	private Set<STATE> oldInitialStates;
	private Collection<STATE> oldFinalStates;

	/* STATEs <-> Integers bijection
	 */
	private HashMap<STATE, Integer> oldStateIndex;
	private ArrayList<STATE> oldState;

	private NWA converted;

	/**
	 * @return NWA generated from input <code>INestedWordAutomaton</code>
	 *         automaton.
	 */
	NWA getNWA() { return converted.clone(); }

	/**
	 * Constructor. Remembers the necessary things about the input
	 * INestedWordAutomaton for later minimization. Stores a NWA converted from
	 * the INestedWordAutomaton.
	 *
	 * @param logger
	 * @param services
	 * @param stateFactory
	 *            the StateFactory that was used to make the states in the
	 *            input automaton
	 * @param automaton
	 *            input INestedWordAutomaton
	 */
	Converter(
			AutomataLibraryServices services,
			StateFactory<STATE> stateFactory,
			INestedWordAutomaton<LETTER, STATE> automaton) {

		this.services = services;
		this.factory = stateFactory;
		this.automaton = automaton;

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

		for (int i = 0; i < numStates; i++)
			isInitial[i] = oldInitialStates.contains(oldState.get(i));

		for (int i = 0; i < numStates; i++)
			isFinal[i] = oldFinalStates.contains(oldState.get(i));

		ArrayList<ITrans> iTrans = new ArrayList<ITrans>();
		ArrayList<CTrans> cTrans = new ArrayList<CTrans>();
		ArrayList<RTrans> rTrans = new ArrayList<RTrans>();

		for (int i = 0; i < numStates; i++) {
			STATE st = oldState.get(i);
			for (OutgoingInternalTransition<LETTER, STATE> x : automaton.internalSuccessors(st)) iTrans.add(new ITrans(i, iSymIndex.get(x.getLetter()), oldStateIndex.get(x.getSucc())));
			for (OutgoingCallTransition<LETTER, STATE>     x : automaton.callSuccessors(st))     cTrans.add(new CTrans(i, cSymIndex.get(x.getLetter()), oldStateIndex.get(x.getSucc())));
			for (OutgoingReturnTransition<LETTER, STATE>   x : automaton.returnSuccessors(st))   rTrans.add(new RTrans(i, rSymIndex.get(x.getLetter()), oldStateIndex.get(x.getHierPred()), oldStateIndex.get(x.getSucc())));
		}

		converted = new NWA();
		converted.numStates = numStates;
		converted.numISyms = numISyms;
		converted.numCSyms = numCSyms;
		converted.numRSyms = numRSyms;
		converted.isInitial = isInitial;
		converted.isFinal = isFinal;
		converted.iTrans = iTrans.toArray(new ITrans[iTrans.size()]);
		converted.cTrans = cTrans.toArray(new CTrans[cTrans.size()]);
		converted.rTrans = rTrans.toArray(new RTrans[rTrans.size()]);
	}

	/**
	 * @param partition
	 *            A (consistent) <code>Partition</code> which represents state
	 *            equivalencies. The number of old states in
	 *            <code>partition</code> (i.e., partition.classOf.length) must
	 *            be consistent with the NWA stored in this Convert instance.
	 *
	 * @return A NestedWordAutomaton constructed from <code>partition</code> and
	 *         from the data which was remembered from the input
	 *         INestedWordAutomaton at construction time.
	 */
	NestedWordAutomaton<LETTER, STATE> constructMerged(Partition partition) {
		assert partition.classOf.length == oldState.size();

		int numclasses = partition.numClasses;
		int[] classOf = partition.classOf;

		/* Avoid duplicate edges in the merged automaton
		 */

		HashSet<ITrans> newITrans = new HashSet<ITrans>();
		HashSet<CTrans> newCTrans = new HashSet<CTrans>();
		HashSet<RTrans> newRTrans = new HashSet<RTrans>();

		for (ITrans x : converted.iTrans) newITrans.add(new ITrans(classOf[x.src], x.sym, classOf[x.dst]));
		for (CTrans x : converted.cTrans) newCTrans.add(new CTrans(classOf[x.src], x.sym, classOf[x.dst]));
		for (RTrans x : converted.rTrans) newRTrans.add(new RTrans(classOf[x.src], x.sym, classOf[x.top], classOf[x.dst]));

		/* For each equivalence class, remember the old STATEs in it
		 */

		ArrayList<ArrayList<STATE>> statesOfclass = new ArrayList<ArrayList<STATE>>();

		for (int i = 0; i < numclasses; i++)
			statesOfclass.add(new ArrayList<STATE>());

		for (int i = 0; i < oldState.size(); i++)
			statesOfclass.get(classOf[i]).add(oldState.get(i));

		for (int i = 0; i < numclasses; i++)
			assert !statesOfclass.get(i).isEmpty();

		/* Make a new STATE for each equivalence class of old STATEs
		 */

		ArrayList<STATE> newState = new ArrayList<STATE>();
		HashSet<STATE> newInitialStates = new HashSet<STATE>();
		HashSet<STATE> newFinalStates = new HashSet<STATE>();

		for (int i = 0; i < numclasses; i++) {
			STATE newst = factory.minimize(statesOfclass.get(i));

			newState.add(newst);

			for (STATE oldst : statesOfclass.get(i)) {
				if (oldInitialStates.contains(oldst))  // any
					newInitialStates.add(newst);
				if (oldFinalStates.contains(oldst))    // all
					newFinalStates.add(newst);
			}
		}

		/* Construct result NestedWordAutomaton
		 */

		NestedWordAutomaton<LETTER, STATE> nwa;
		nwa = new NestedWordAutomaton<LETTER, STATE>(services, iAlphabet, cAlphabet, rAlphabet, factory);

		for (STATE st : newState)
			nwa.addState(newInitialStates.contains(st), newFinalStates.contains(st), st);

		for (ITrans x : newITrans)
			nwa.addInternalTransition(newState.get(x.src), iSym.get(x.sym), newState.get(x.dst));

		for (CTrans x : newCTrans)
			nwa.addCallTransition(newState.get(x.src), cSym.get(x.sym), newState.get(x.dst));

		for (RTrans x : newRTrans)
			nwa.addReturnTransition(newState.get(x.src), newState.get(x.top), rSym.get(x.sym), newState.get(x.dst));

		return nwa;
	}

	/* Compute history states, using a INestedWordAutomaton based implementation
	 */

	ArrayList<Hist> computeHistoryStates() {
		STATE bottomOfStackState = automaton.getEmptyStackState();
		ArrayList<Hist> hist = new ArrayList<Hist>();

		/* casting doesn't really make sense here, but it seems this is
		 * currently the only implementation of history states
		 */
		if (!(automaton instanceof IDoubleDeckerAutomaton<?, ?>))
			throw new IllegalArgumentException("Operand must be an IDoubleDeckerAutomaton.");

		IDoubleDeckerAutomaton<LETTER, STATE> doubleDecker;
		doubleDecker = (IDoubleDeckerAutomaton<LETTER, STATE>) automaton;

		for (int i = 0; i < oldState.size(); i++) {
			if (doubleDecker.isDoubleDecker(oldState.get(i), bottomOfStackState))
				hist.add(new Hist(i, -1));  // -1 is bottom-of-stack

			for (int j = 0; j < oldState.size(); j++)
				if (doubleDecker.isDoubleDecker(oldState.get(i), oldState.get(j)))
					hist.add(new Hist(i, j));
		}

		return hist;
	}
}
