/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.util.AbstractCollection;
import java.util.AbstractSet;
import java.util.Collection;
import java.util.Deque;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTrigger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.TriggerExecutionContext;


/**
 * Special yield trigger implementation to delay instantiation of the expensive
 * read over write axiom.  DO NOT USE OTHERWISE!!!
 * @author Juergen Christ
 */
public class ArrayYieldTrigger extends YieldTrigger {

	private static class ArrayInstMap implements Map<TermVariable, Integer> {
		private static class Entry implements Map.Entry<TermVariable, Integer> {
			TermVariable m_var;
			int m_val;
			public Entry(TermVariable var, int pos) {
				m_var = var;
				m_val = pos;
			}

			@Override
			public TermVariable getKey() {
				return m_var;
			}

			@Override
			public Integer getValue() {
				return m_val;
			}

			@Override
			public Integer setValue(Integer value) {
				throw new UnsupportedOperationException();
			}
			
		}
		Entry[] entries;
		public ArrayInstMap(TermVariable arr,TermVariable val,
				TermVariable idx1,TermVariable idx2,int arrpos,int valpos,
				int idx1pos,int idx2pos) {
			entries = new Entry[] {
					new Entry(arr,arrpos),
					new Entry(val,valpos),
					new Entry(idx1,idx1pos),
					new Entry(idx2,idx2pos)
			};
		}
		
		public int getArrayIdx() {
			return entries[0].getValue();
		}
		
		public int getValueIdx() {
			return entries[1].getValue();
		}
		
		public int getIdx1Idx() {
			return entries[2].getValue();
		}
		
		public int getIdx2Idx() {
			return entries[3].getValue();
		}

		@Override
		public void clear() {}

		@Override
		public boolean containsKey(Object key) {
			if (!(key instanceof TermVariable))
				return false;
			for (Entry e : entries) {
				if (e.getKey() == key)
					return true;
			}
			return false;
		}

		@Override
		public boolean containsValue(Object value) {
			if (!(value instanceof Integer))
				return false;
			for (Entry e : entries) {
				if (e.getValue().equals(value))
					return true;
			}
			return false;
		}

		@Override
		public Set<java.util.Map.Entry<TermVariable, Integer>> entrySet() {
			return new AbstractSet<Map.Entry<TermVariable,Integer>>() {

				@Override
				public Iterator<java.util.Map.Entry<TermVariable, Integer>> iterator() {
					return new Iterator<Map.Entry<TermVariable,Integer>>() {
						int i = 0;
						@Override
						public boolean hasNext() {
							return i < entries.length;
						}

						@Override
						public java.util.Map.Entry<TermVariable, Integer> next() {
							return entries[i++];
						}

						@Override
						public void remove() {
							throw new UnsupportedOperationException();
						}
					};
				}

				@Override
				public int size() {
					return entries.length;
				}
				
			};
		}

		@Override
		public Integer get(Object key) {
			for (Entry e : entries) {
				if (e.getKey() == key)
					return e.getValue();
			}
			return null;
		}

		@Override
		public boolean isEmpty() {
			return false;
		}

		@Override
		public Set<TermVariable> keySet() {
			return new AbstractSet<TermVariable>() {

				@Override
				public Iterator<TermVariable> iterator() {
					return new Iterator<TermVariable>() {
						int i = 0;
						@Override
						public boolean hasNext() {
							return i < entries.length;
						}

						@Override
						public TermVariable next() {
							return entries[i++].getKey();
						}

						@Override
						public void remove() {
							throw new UnsupportedOperationException();
						}
						
					};
				}

				@Override
				public int size() {
					return entries.length;
				}
				
			};
		}

		@Override
		public Integer put(TermVariable key, Integer value) {
			throw new UnsupportedOperationException();
		}

		@Override
		public void putAll(Map<? extends TermVariable, ? extends Integer> m) {
			throw new UnsupportedOperationException();
		}

		@Override
		public Integer remove(Object key) {
			throw new UnsupportedOperationException();
		}

		@Override
		public int size() {
			return entries.length;
		}

		@Override
		public Collection<Integer> values() {
			return new AbstractCollection<Integer>() {
				@Override
				public Iterator<Integer> iterator() {
					return new Iterator<Integer>() {
						int i = 0;
						@Override
						public boolean hasNext() {
							return i < entries.length;
						}

						@Override
						public Integer next() {
							return entries[i++].getValue();
						}

						@Override
						public void remove() {
							throw new UnsupportedOperationException();							
						}
						
					};
				}

				@Override
				public int size() {
					return entries.length;
				}
				
			};
		}
	}
	ArrayInstMap m_map;
	public ArrayYieldTrigger(TermVariable arr,TermVariable val,
			TermVariable idx1,TermVariable idx2,int arrpos,int valpos,
			int idx1pos,int idx2pos) {
		super(new ArrayInstMap(arr,val,idx1,idx2,arrpos,valpos,idx1pos,idx2pos));
		m_map = (ArrayInstMap) super.substitution;
	}
	
	@Override
	public void match(CClosure engine, CCTerm[] regs, List<CCTrigger> path,
			int pos, TriggerExecutionContext tec, Deque<Object> unused) {
		assert(tec != null);
		// Do the "reactivation check" here
		if (tec.isPassive())
			return;
		tec.passivate();
		engine.yieldDone(tec);
		if (!knownSubsts.createInstantiation(regs, substitution,
				converter.dpllEngine.getLogger(),quantsub))
			return;
//		converter.getCClosure().addArrayInst(regs[m_map.getArrayIdx()],
//				regs[m_map.getValueIdx()], regs[m_map.getIdx1Idx()],
//				regs[m_map.getIdx2Idx()], this);
	}
	private static CCTerm[] regs = new CCTerm[4];
	public void instantiate(CCTerm arr,CCTerm val,CCTerm idx1,CCTerm idx2) {
		regs[m_map.getArrayIdx()] = arr;
		regs[m_map.getValueIdx()] = val;
		regs[m_map.getIdx1Idx()] = idx1;
		regs[m_map.getIdx2Idx()] = idx2;
		instantiate(regs);
	}

}
