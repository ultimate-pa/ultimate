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

package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion;

import java.util.ArrayList;
import java.util.List;

import gnu.trove.iterator.TIntObjectIterator;
import gnu.trove.map.TIntObjectMap;
import gnu.trove.map.hash.TIntObjectHashMap;

public class Antichain {
    
    private TIntObjectMap<List<DifferencePair>> mPairMap;
    
    public Antichain() {
        mPairMap = new TIntObjectHashMap<>();
    }
    
    public boolean addPair(DifferencePair pair) {
        
        final int fstState = pair.getFirstState();
        List<DifferencePair> sndElem = mPairMap.get(fstState);
        
        if(sndElem == null) {
            sndElem = new ArrayList<>();
        }
        List<DifferencePair> copy = new ArrayList<>();
        //avoid to add pairs are covered by other pairs
        for(int i = 0; i < sndElem.size(); i ++) {
            DifferencePair elem = sndElem.get(i);
            //pairs covered by the new pair
            //will not be kept in copy
            if(elem.coveredBy(pair)) {
                continue;
            }else if(pair.coveredBy(elem)) {
                return false;
            }
            copy.add(elem);
        }
        
        copy.add(pair); // should add snd
        mPairMap.put(fstState, copy);
        return true;
    }
    
    public boolean covers(DifferencePair pair) {
        List<DifferencePair> sndElem = mPairMap.get(pair.getFirstState());
        if(sndElem == null) return false;
        for(int i = 0; i < sndElem.size(); i ++) {
            DifferencePair elem = sndElem.get(i);
            if(pair.coveredBy(elem)) { // no need to add it
                return true;
            }
        }
        return false;
    }
    
    public String toString() {
        StringBuilder sb = new StringBuilder();
        TIntObjectIterator<List<DifferencePair>> iter = mPairMap.iterator();
        while(iter.hasNext()) {
            iter.advance();
            sb.append(iter.key() + " -> " + iter.value() + "\n");
        }
        return sb.toString();
    }
    
    public int size() {
        int num = 0;
        TIntObjectIterator<List<DifferencePair>> iter = mPairMap.iterator();
        while(iter.hasNext()) {
            iter.advance();
            num += iter.value().size();
        }
        return num;
    }

}
