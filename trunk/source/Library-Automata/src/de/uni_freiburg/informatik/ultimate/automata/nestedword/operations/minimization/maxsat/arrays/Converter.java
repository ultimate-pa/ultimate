/*
 * Copyright (C) 2016 Jens Stimpfle <stimpflj@informatik.uni-freiburg.de>

 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 3 of the License,
 * or (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be
 * useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser
 * General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see
 * <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automata Library, or any covered work, by linking or combining it
 * with Eclipse RCP (or a modified version of Eclipse RCP), containing parts
 * covered by the terms of the Eclipse Public License, the licensors of the
 * ULTIMATE Automata Library grant you additional permission to convey the
 * resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.arrays;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;

/**
 * Convert a <code>INestedWordAutomaton</code> to a <code>NWA</code> structure. Using the <code>constructMerged()</code>
 * method, a smaller equivalent <code>NestedWordAutomaton</code> can be made later given a <code>Partition</code>
 * structure.
 *
 * @author stimpflj
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
final class Converter<LETTER, STATE> {

	private final AutomataLibraryServices mServices;
	private final IMergeStateFactory<STATE> mFactory;
	private final INestedWordAutomaton<LETTER, STATE> mAutomaton;

	/* LETTERs are shared between old (input) and new (output) automaton
	 */
	private final Set<LETTER> mIAlphabet;
	private final Set<LETTER> mCAlphabet;
	private final Set<LETTER> mRAlphabet;

	/* LETTERs <-> Integers bijection
	 */
	private final HashMap<LETTER, Integer> mISymIndex;
	private final HashMap<LETTER, Integer> mCSymIndex;
	private final HashMap<LETTER, Integer> mRSymIndex;
	private final ArrayList<LETTER> mISym;
	private final ArrayList<LETTER> mCSym;
	private final ArrayList<LETTER> mRSym;

	/* STATEs are *not* shared between old and new automaton
	 */
	private final Set<STATE> mOldStates;
	private final Set<STATE> mOldInitialStates;
	private final Collection<STATE> mOldFinalStates;

	/* STATEs <-> Integers bijection
	 */
	private final HashMap<STATE, Integer> mOldStateIndex;
	private final ArrayList<STATE> mOldState;

	private final NwaWithArrays mConverted;

	/**
	 * Constructor. Remembers the necessary things about the input INestedWordAutomaton for later minimization. Stores a
	 * NWA converted from the INestedWordAutomaton.
	 *
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            the StateFactory that was used to make the states in the input automaton
	 * @param automaton
	 *            input INestedWordAutomaton
	 */
	Converter(final AutomataLibraryServices services, final IMergeStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> automaton) {

		this.mServices = services;
		this.mFactory = stateFactory;
		this.mAutomaton = automaton;

		mOldStates = automaton.getStates();
		mOldInitialStates = automaton.getInitialStates();
		mOldFinalStates = automaton.getFinalStates();

		mIAlphabet = automaton.getVpAlphabet().getInternalAlphabet();
		mCAlphabet = automaton.getVpAlphabet().getCallAlphabet();
		mRAlphabet = automaton.getVpAlphabet().getReturnAlphabet();

		mOldStateIndex = new HashMap<>();
		mOldState = new ArrayList<>();

		mISymIndex = new HashMap<>();
		mCSymIndex = new HashMap<>();
		mRSymIndex = new HashMap<>();

		mISym = new ArrayList<>();
		mCSym = new ArrayList<>();
		mRSym = new ArrayList<>();

		for (final STATE st : mOldStates) {
			assert !mOldStateIndex.containsKey(st);
			final int idx = mOldState.size();
			mOldStateIndex.put(st, idx);
			mOldState.add(st);
		}

		for (final LETTER isym : mIAlphabet) {
			assert !mISymIndex.containsKey(isym);
			final int idx = mISym.size();
			mISymIndex.put(isym, idx);
			mISym.add(isym);
		}

		for (final LETTER csym : mCAlphabet) {
			assert !mCSymIndex.containsKey(csym);
			final int idx = mCSym.size();
			mCSymIndex.put(csym, idx);
			mCSym.add(csym);
		}

		for (final LETTER rsym : mRAlphabet) {
			assert !mRSymIndex.containsKey(rsym);
			final int idx = mRSym.size();
			mRSymIndex.put(rsym, idx);
			mRSym.add(rsym);
		}

		final int numStates = mOldState.size();
		final int numISyms = mISym.size();
		final int numCSyms = mCSym.size();
		final int numRSyms = mRSym.size();

		final boolean[] isInitial = new boolean[numStates];
		final boolean[] isFinal = new boolean[numStates];

		for (int i = 0; i < numStates; i++) {
			isInitial[i] = mOldInitialStates.contains(mOldState.get(i));
		}

		for (int i = 0; i < numStates; i++) {
			isFinal[i] = mOldFinalStates.contains(mOldState.get(i));
		}

		final ArrayList<ITrans> iTrans = new ArrayList<>();
		final ArrayList<CTrans> cTrans = new ArrayList<>();
		final ArrayList<RTrans> rTrans = new ArrayList<>();

		for (int i = 0; i < numStates; i++) {
			final STATE st = mOldState.get(i);
			for (final OutgoingInternalTransition<LETTER, STATE> x : automaton.internalSuccessors(st)) {
				iTrans.add(new ITrans(i, mISymIndex.get(x.getLetter()), mOldStateIndex.get(x.getSucc())));
			}
			for (final OutgoingCallTransition<LETTER, STATE> x : automaton.callSuccessors(st)) {
				cTrans.add(new CTrans(i, mCSymIndex.get(x.getLetter()), mOldStateIndex.get(x.getSucc())));
			}
			for (final OutgoingReturnTransition<LETTER, STATE> x : automaton.returnSuccessors(st)) {
				rTrans.add(new RTrans(i, mRSymIndex.get(x.getLetter()), mOldStateIndex.get(x.getHierPred()),
						mOldStateIndex.get(x.getSucc())));
			}
		}

		mConverted = new NwaWithArrays();
		mConverted.mNumStates = numStates;
		mConverted.mNumISyms = numISyms;
		mConverted.mNumCSyms = numCSyms;
		mConverted.mNumRSyms = numRSyms;
		mConverted.mIsInitial = isInitial;
		mConverted.mIsFinal = isFinal;
		mConverted.mITrans = iTrans.toArray(new ITrans[iTrans.size()]);
		mConverted.mCTrans = cTrans.toArray(new CTrans[cTrans.size()]);
		mConverted.mRTrans = rTrans.toArray(new RTrans[rTrans.size()]);
	}

	/**
	 * @return NWA generated from input <code>INestedWordAutomaton</code> automaton.
	 */
	NwaWithArrays getNwa() {
		return mConverted.clone();
	}

	/**
	 * @param partition
	 *            A (consistent) <code>Partition</code> which represents state equivalencies. The number of old states
	 *            in <code>partition</code> (i.e., partition.classOf.length) must be consistent with the NWA stored in
	 *            this Convert instance.
	 * @return A NestedWordAutomaton constructed from <code>partition</code> and from the data which was remembered from
	 *         the input INestedWordAutomaton at construction time.
	 */
	INestedWordAutomaton<LETTER, STATE> constructMerged(final Partition partition) {
		assert partition.mClassOf.length == mOldState.size();

		final int numclasses = partition.mNumClasses;
		final int[] classOf = partition.mClassOf;

		/* Avoid duplicate edges in the merged automaton
		 */

		final HashSet<ITrans> newITrans = new HashSet<>();
		final HashSet<CTrans> newCTrans = new HashSet<>();
		final HashSet<RTrans> newRTrans = new HashSet<>();

		for (final ITrans x : mConverted.mITrans) {
			newITrans.add(new ITrans(classOf[x.mSrc], x.mSym, classOf[x.mDst]));
		}
		for (final CTrans x : mConverted.mCTrans) {
			newCTrans.add(new CTrans(classOf[x.mSrc], x.mSym, classOf[x.mDst]));
		}
		for (final RTrans x : mConverted.mRTrans) {
			newRTrans.add(new RTrans(classOf[x.mSrc], x.mSym, classOf[x.mTop], classOf[x.mDst]));
		}

		/* For each equivalence class, remember the old STATEs in it
		 */

		final ArrayList<ArrayList<STATE>> statesOfclass = new ArrayList<>();

		for (int i = 0; i < numclasses; i++) {
			statesOfclass.add(new ArrayList<STATE>());
		}

		for (int i = 0; i < mOldState.size(); i++) {
			statesOfclass.get(classOf[i]).add(mOldState.get(i));
		}

		for (int i = 0; i < numclasses; i++) {
			assert !statesOfclass.get(i).isEmpty();
		}

		/* Make a new STATE for each equivalence class of old STATEs
		 */

		final ArrayList<STATE> newState = new ArrayList<>();
		final HashSet<STATE> newInitialStates = new HashSet<>();
		final HashSet<STATE> newFinalStates = new HashSet<>();

		for (int i = 0; i < numclasses; i++) {
			final STATE newst = mFactory.merge(statesOfclass.get(i));

			newState.add(newst);

			for (final STATE oldst : statesOfclass.get(i)) {
				if (mOldInitialStates.contains(oldst)) {
					newInitialStates.add(newst);
				}
				if (mOldFinalStates.contains(oldst)) {
					newFinalStates.add(newst);
				}
			}
		}

		/* Construct result NestedWordAutomaton
		 */

		NestedWordAutomaton<LETTER, STATE> nwa;
		nwa = new NestedWordAutomaton<LETTER, STATE>(mServices, new VpAlphabet<>(mIAlphabet, mCAlphabet, mRAlphabet), mFactory);

		for (final STATE st : newState) {
			nwa.addState(newInitialStates.contains(st), newFinalStates.contains(st), st);
		}

		for (final ITrans x : newITrans) {
			nwa.addInternalTransition(newState.get(x.mSrc), mISym.get(x.mSym), newState.get(x.mDst));
		}

		for (final CTrans x : newCTrans) {
			nwa.addCallTransition(newState.get(x.mSrc), mCSym.get(x.mSym), newState.get(x.mDst));
		}

		for (final RTrans x : newRTrans) {
			nwa.addReturnTransition(newState.get(x.mSrc), newState.get(x.mTop), mRSym.get(x.mSym),
					newState.get(x.mDst));
		}

		return nwa;
	}

	/* Compute history states, using a INestedWordAutomaton based implementation
	 */

	ArrayList<Hist> computeHistoryStates() {
		/* casting doesn't really make sense here, but it seems this is
		 * currently the only implementation of history states
		 */
		if (!(mAutomaton instanceof IDoubleDeckerAutomaton<?, ?>)) {
			throw new IllegalArgumentException("Operand must be an IDoubleDeckerAutomaton.");
		}

		IDoubleDeckerAutomaton<LETTER, STATE> doubleDecker;
		doubleDecker = (IDoubleDeckerAutomaton<LETTER, STATE>) mAutomaton;

		final STATE bottomOfStackState = mAutomaton.getEmptyStackState();
		final ArrayList<Hist> hist = new ArrayList<>();
		for (int i = 0; i < mOldState.size(); i++) {
			if (doubleDecker.isDoubleDecker(mOldState.get(i), bottomOfStackState)) {
				// -1 is bottom-of-stack
				hist.add(new Hist(i, -1));
			}

			for (int j = 0; j < mOldState.size(); j++) {
				if (doubleDecker.isDoubleDecker(mOldState.get(i), mOldState.get(j))) {
					hist.add(new Hist(i, j));
				}
			}
		}

		return hist;
	}
}
