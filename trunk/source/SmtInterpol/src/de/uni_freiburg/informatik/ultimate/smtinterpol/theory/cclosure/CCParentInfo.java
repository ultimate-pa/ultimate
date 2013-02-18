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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAppTerm.Parent;

/**
 * This class collects various information for an equivalence class 
 * of CCTerms about function applications on the terms in the class.
 * The informations are:
 * <ul><li>The AppTerm that have a CCTerm in the equivalence class as
 * func or app subterm.</li>
 * <li>The reverse triggers that search for a function application on
 * the equivalence class.</li>
 * </ul>
 * 
 * To allow faster searches for the relevant information, the information
 * is ordered by the function symbol and position of the the argument.
 * This is realised by the member <code>mFuncSymbNr</code> that uniquely
 * defines the function symbol and the position of the argument.  The 
 * <code>mFuncSymbNr</code> is 0 if this represents the func child of some
 * appterm.  Since all the things in that class are partial application of
 * the same function, the mFuncSymbNr is not needed in that case.
 * 
 * The CCParentInfo build a linked list sorted by <code>mFuncSymbNr</code>.
 * The CCTerm stores only the first element of the list, the 
 * <code>mNext</code> field points to the next element in the linked list.
 *  
 * When equivalence classes are merged, their corresponding 
 * <code>CCParentInfo</code>s are merged, too.  The list for the new 
 * representative is changed.  Currently new CCParentInfo are created for
 * the new representative, however, the contents are just shared with the
 * list of the old representative.  We use the usual joinList/unjoinList 
 * paradigm for the contents of the parent info.
 * 
 * @author hoenicke
 *
 */
public class CCParentInfo {
	int m_FuncSymbNr;
	SimpleList<Parent> m_CCParents;
	CCParentInfo m_Next;
	
	/**
	 * Create an empty CCParentInfo as list head.
	 */
	public CCParentInfo() {
		m_FuncSymbNr = -1;
	}

	private CCParentInfo(int funcSymbNr, CCParentInfo next) {
		m_FuncSymbNr = funcSymbNr;
		m_CCParents = new SimpleList<Parent>();
		m_Next = next;
	}
	
	private CCParentInfo(CCParentInfo other, CCParentInfo next) {
		this(other.m_FuncSymbNr, next);
		m_CCParents.joinList(other.m_CCParents);
	}
	
	public void addParentInfo(int funcSymbNr, Parent parent, boolean isLast, CClosure engine) {
		CCParentInfo info = this;
		while (info.m_Next != null && info.m_Next.m_FuncSymbNr <= funcSymbNr) {
			info = info.m_Next;
			if (info.m_FuncSymbNr == funcSymbNr) {
				info.m_CCParents.prependIntoJoined(parent, isLast);
				return;
			}
		}
		info.m_Next = new CCParentInfo(funcSymbNr, info.m_Next);
		info.m_Next.m_CCParents.prependIntoJoined(parent, isLast);
	}
	
	public void mergeParentInfo(CCParentInfo other) {
		CCParentInfo myInfo = this;
		// skip head
		other = other.m_Next;
		while (other != null) {
			int funcSymbNr = other.m_FuncSymbNr;
//			assert !other.m_CCParents.isEmpty() || !other.m_ReverseTriggers.isEmpty();
			while (myInfo.m_Next != null && myInfo.m_Next.m_FuncSymbNr < funcSymbNr) {
				myInfo = myInfo.m_Next;
			}
			if (myInfo.m_Next != null && myInfo.m_Next.m_FuncSymbNr == funcSymbNr) {
				/* merge infos */
				myInfo = myInfo.m_Next;
				myInfo.m_CCParents.joinList(other.m_CCParents);
			} else {
				/* copy info */
				/* FIXME: can we move info instead??  It saves creating lots of 
				 * objects but really complicates things */
				myInfo.m_Next = new CCParentInfo(other, myInfo.m_Next);
				myInfo = myInfo.m_Next;
			}
			other = other.m_Next;
		}
	}
	
	public void unmergeParentInfo(CCParentInfo other) {
		CCParentInfo myInfo = this;
		// skip head
		other = other.m_Next;
		while (other != null) {
			int funcSymbNr = other.m_FuncSymbNr;
//			assert !other.m_CCParents.isEmpty() || !other.m_ReverseTriggers.isEmpty();
			while (myInfo.m_Next.m_FuncSymbNr < funcSymbNr) {
				myInfo = myInfo.m_Next;
			}
			CCParentInfo next = myInfo.m_Next;
			assert (next.m_FuncSymbNr == funcSymbNr);
			
			/* unjoin lists */
			next.m_CCParents.unjoinList(other.m_CCParents);
			/* FIXME: Do we really want to remove the entry if it gets empty?? 
			 * OTOH, we would then need to create a new info more often.
			 */
			if (next.m_CCParents.isEmpty()) {
				;//myInfo.m_Next = next.m_Next;
			} else {
				myInfo = next;
			}
			other = other.m_Next;
		}
	}

	CCParentInfo getInfo(int funcSymbNr) {
		CCParentInfo info = this;
		while (info.m_Next != null && info.m_Next.m_FuncSymbNr <= funcSymbNr) {
			info = info.m_Next;
			if (info.m_FuncSymbNr == funcSymbNr) {
				return info;
			}
		}
		return null;
	}
	
	CCParentInfo createInfo(int funcSymbNr) {
		CCParentInfo info = this;
		while (info.m_Next != null && info.m_Next.m_FuncSymbNr <= funcSymbNr) {
			info = info.m_Next;
			if (info.m_FuncSymbNr == funcSymbNr) {
				return info;
			}
		}
		return info.m_Next = new CCParentInfo(funcSymbNr, info.m_Next);
	}
	
	CCParentInfo getExistingParentInfo(int funcSymbNr) {
		CCParentInfo info = this;
		while (info.m_Next != null && info.m_Next.m_FuncSymbNr <= funcSymbNr) {
			info = info.m_Next;
			if (info.m_FuncSymbNr == funcSymbNr) {
				return info;
			}
		}
		return null;
	}
	
	public SimpleList<Parent> getParentInfo(int funcSymbNr) {
		CCParentInfo info = m_Next;
		while (info != null && info.m_FuncSymbNr < funcSymbNr)
			info = info.m_Next;
		if (info != null && info.m_FuncSymbNr == funcSymbNr)
			return info.m_CCParents;
		return new SimpleList<Parent>();
	}
}
