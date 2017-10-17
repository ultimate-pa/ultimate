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

package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;
import gnu.trove.map.TIntObjectMap;
import gnu.trove.map.hash.TIntObjectHashMap;



public class AccGenBuchi implements Acc {

    protected final TIntObjectMap<IntSet> mAccStateMap;
    protected final int mAccSize;
    
    public AccGenBuchi(int size) {
    	mAccStateMap = new TIntObjectHashMap<>();
    	mAccSize = size;
    }
    
    public AccGenBuchi(IntSet finalStates) {
    	mAccStateMap = new TIntObjectHashMap<>();
    	mAccSize = AccBuchi.ACC_SIZE_ONE;
    	mAccStateMap.put(AccBuchi.ACC_LABEL_ZERO, finalStates.clone());
    }
    
    @Override
    public boolean isAccepted(IntSet set) {
    	IntSet labels = UtilIntSet.newIntSet();
        for(int state : set.iterable()) {
        	IntSet lab = mAccStateMap.get(state);
            if(lab == null) continue;
            labels.or(lab);
            if(labels.cardinality() == mAccSize)
            	return true;
        }
        return false;
    }

    @Override
    public IntSet getLabels(int state) {
        IntSet labels = mAccStateMap.get(state);
        if(labels == null) {
        	labels = UtilIntSet.newIntSet();
        }else {
        	labels = labels.clone();
        }
        return labels;
    }
    
    @Override
    public void setLabel(int state, int label) {
    	assert checkLabelConsistency(label);
    	IntSet labels = mAccStateMap.get(state);
    	if(labels == null) {
    		labels = UtilIntSet.newIntSet();
    	}
    	labels.set(label);
    	mAccStateMap.put(state, labels);
    }
    
    @Override
    public void setLabel(int state, IntSet labels) {
    	if(labels == null) return ;
    	IntSet result = mAccStateMap.get(state);
    	if(result == null) {
    		result = UtilIntSet.newIntSet();
    	}
    	assert checkLabelConsistency(labels);
    	result.or(labels);
    	mAccStateMap.put(state, result);
    }
    
    @Override
    public int getAccSize() {
    	return mAccSize;
    }
    
    private boolean checkLabelConsistency(IntSet labels) {
    	for(int label : labels.iterable()) {
    		if(! checkLabelConsistency(label))
    			return false;
    	}
    	return true;
    }
    
    private boolean checkLabelConsistency(int label) {
    	return label >= 0 && label < mAccSize;
    }
    
}
