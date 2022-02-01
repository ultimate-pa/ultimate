/*
 * Copyright (C) 2017 Yong Li (liyong@ios.ac.cn)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.complement;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.Options;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.BuchiNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IBuchiNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IStateNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntIterator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;
import gnu.trove.map.TObjectIntMap;
import gnu.trove.map.hash.TObjectIntHashMap;



/**
 * Only valid for semi-deterministic Buchi nesed word automata
 */
public class BuchiNwaComplement extends BuchiNwa implements IBuchiNwaComplement {

    private final IBuchiNwa mOperand;
    private final TObjectIntMap<DoubleDecker> mDeckerMap;
    private final List<DoubleDecker> mDeckerList;

    private final TObjectIntMap<StateNwaNCSB> mStateIndices = new TObjectIntHashMap<>();
    private final IntSet mFinalDeckers;

    public BuchiNwaComplement(IBuchiNwa buchi) {
        super(buchi.getAlphabetCall(), buchi.getAlphabetInternal(), buchi.getAlphabetReturn());
        this.mOperand = buchi;
        this.mDeckerMap = new TObjectIntHashMap<>();
        this.mDeckerList = new ArrayList<>();
        this.mFinalDeckers = UtilIntSet.newIntSet();
        computeInitialStates();
    }

    private void computeInitialStates() {
        IntSet upC = mOperand.getInitialStates().clone();
        upC.and(mOperand.getFinalStates()); // goto C
        IntSet upN = mOperand.getInitialStates().clone();
        upN.andNot(upC);
        IntSet N = generateDeckers(DoubleDecker.EMPTY_DOWN_STATE, upN);
        IntSet C = generateDeckers(DoubleDecker.EMPTY_DOWN_STATE, upC);
        NCSB ncsb = new NCSB(N, C, UtilIntSet.newIntSet(), C);
        StateNwaNCSB state = new StateNwaNCSB(this, 0, ncsb);
        if (C.isEmpty())
            this.setFinal(0);
        this.setInitial(0);
        int id = this.addState(state);
        mStateIndices.put(state, id);
    }

    protected StateNwaNCSB addState(NCSB ncsb) {

        StateNwaNCSB state = new StateNwaNCSB(this, 0, ncsb);

        if (mStateIndices.containsKey(state)) {
            return (StateNwaNCSB) getState(mStateIndices.get(state));
        } else {
            int index = getStateSize();
            StateNwaNCSB newState = new StateNwaNCSB(this, index, ncsb);
            int id = this.addState(newState);
            mStateIndices.put(newState, id);
            if (ncsb.getBSet().isEmpty())
                setFinal(index);
            return newState;
        }
    }

    @Override
    public IBuchiNwa getOperand() {
        return mOperand;
    }

    @Override
    public DoubleDecker getDoubleDecker(int id) {
        assert id < mDeckerList.size();
        return mDeckerList.get(id);
    }

    @Override
    public int getDoubleDeckerId(DoubleDecker decker) {
        if (mDeckerMap.containsKey(decker)) {
            return mDeckerMap.get(decker);
        }
        int id = mDeckerList.size();
        mDeckerList.add(decker);
        mDeckerMap.put(decker, id);
        if (mOperand.isFinal(decker.getUpState())) {
            mFinalDeckers.set(id);
        }
        return id;
    }

    protected IntSet getFinalDeckers() {
        return mFinalDeckers;
    }

    protected IntSet generateDeckers(int downState, IntSet upStates) {
        IntSet result = UtilIntSet.newIntSet();
        for (final int upState : upStates.iterable()) {
            result.set(getDoubleDeckerId(new DoubleDecker(downState, upState)));
        }
        return result;
    }

    public int getUpState(int decker) {
        return getDoubleDecker(decker).getUpState();
    }

    public int getDownState(int decker) {
        return getDoubleDecker(decker).getDownState();
    }

    // ------------------- following is not needed
    private boolean mExplored = false;

    // TODO: removed
    public void explore() {

        if (mExplored)
            return;

        mExplored = true;

        LinkedList<IStateNwa> walkList = new LinkedList<>();
        IntSet initialStates = getInitialStates();

        IntIterator iter = initialStates.iterator();
        while (iter.hasNext()) {
            walkList.addFirst(getState(iter.next()));
        }

        BitSet visited = new BitSet();

        Set<Integer> callPreds = new HashSet<>();

        while (!walkList.isEmpty()) {
            IStateNwa s = walkList.remove();
            if (visited.get(s.getId()))
                continue;
            visited.set(s.getId());
            if (Options.verbose)
                System.out.println("s" + s.getId() + ": " + s.toString());
            // call alphabets
            IntSet calls = mOperand.getAlphabetCall();
            IntIterator iterLetter = calls.iterator();
            while (iterLetter.hasNext()) {
                int letter = iterLetter.next();
                IntSet succs = s.getSuccessorsCall(letter);
                if (!succs.isEmpty())
                    callPreds.add(s.getId());
                exploreSuccessors(s, walkList, succs, visited, letter);
            }

            iterLetter = mOperand.getAlphabetInternal().iterator();
            while (iterLetter.hasNext()) {
                int letter = iterLetter.next();
                if (s.getId() == 6 && letter == 4) {
                    System.out.println("HAHA");
                }
                IntSet succs = s.getSuccessorsInternal(letter);
                exploreSuccessors(s, walkList, succs, visited, letter);
            }

            iterLetter = mOperand.getAlphabetReturn().iterator();

            while (iterLetter.hasNext()) {
                // System.out.println(callPreds);
                int letter = iterLetter.next();
                //
                int size = getStateSize();
                for (int i = 0; i < size; i++) {
                    for (Integer hier : callPreds) {
                        IStateNwa state = getState(i);
                        if (Options.verbose)
                            System.out.println("current: " + state.toString() + "  hier: " + hier + " :"
                                    + getState(hier).toString());
                        IntSet succs = state.getSuccessorsReturn(hier, letter);
                        exploreSuccessors(state, walkList, succs, visited, letter);
                    }
                }

            }
        }

        // System.out.println("" + getStates());
    }

    private void exploreSuccessors(IStateNwa s, LinkedList<IStateNwa> walkList, IntSet succs, BitSet visited,
            int letter) {
        IntIterator iter = succs.iterator();
        while (iter.hasNext()) {
            int n = iter.next();
            // if(Options.verbose) System.out.println("size of deckers: " +
            // mDeckerList.size() + " " + mDeckerList.toString());
            if (Options.verbose)
                System.out.println(
                        " s" + s.getId() + ": " + s.toString() + "- L" + letter + " -> s" + n + ": " + getState(n));
            if (!visited.get(n)) {
                walkList.addFirst(getState(n));
            }
        }
    }

}
