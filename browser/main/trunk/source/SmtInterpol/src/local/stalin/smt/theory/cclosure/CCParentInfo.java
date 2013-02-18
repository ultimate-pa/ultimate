package local.stalin.smt.theory.cclosure;

import local.stalin.smt.dpll.SimpleList;
import local.stalin.smt.theory.cclosure.CCAppTerm.Parent;

public class CCParentInfo {
	int mFuncSymbNr;
	SimpleList<Parent> mCCParents;
	CCParentInfo mNext;
	
	/**
	 * Create an empty CCParentInfo as list head.
	 */
	public CCParentInfo() {
		mFuncSymbNr = -1;
	}

	/**
	 * Create a new Parent info.
	 * @param funcSymbNr
	 * @param ccParent
	 * @param next
	 */
	public CCParentInfo(int funcSymbNr, Parent ccParent, 
			CCParentInfo next) {
		mFuncSymbNr = funcSymbNr;
		mCCParents = new SimpleList<Parent>();
		mCCParents.append(ccParent);
		mNext = next;
	}

	public CCParentInfo(int funcSymbNr, SimpleList<Parent> ccParent, 
			CCParentInfo next) {
		mFuncSymbNr = funcSymbNr;
		mCCParents = ccParent;
		mNext = next;
	}
	
	public void addParentInfo(int funcSymbNr, Parent parent) {
		CCParentInfo info = this;
		while (info.mNext != null && info.mNext.mFuncSymbNr <= funcSymbNr) {
			info = info.mNext;
			if (info.mFuncSymbNr == funcSymbNr) {
				info.mCCParents.append(parent);
				return;
			}
		}
		info.mNext = new CCParentInfo(funcSymbNr, parent, info.mNext);
	}


	public void mergeParentInfo(CCParentInfo other) {
		CCParentInfo myInfo = this;
		// skip head
		other = other.mNext;
		while (other != null) {
			int funcSymbNr = other.mFuncSymbNr;
			while (myInfo.mNext != null && myInfo.mNext.mFuncSymbNr < funcSymbNr) {
				myInfo = myInfo.mNext;
			}
			if (myInfo.mNext != null && myInfo.mNext.mFuncSymbNr == funcSymbNr) {
				/* merge infos */
				myInfo = myInfo.mNext;
				myInfo.mCCParents.joinList(other.mCCParents);
			} else {
				/* move info */
				myInfo.mNext = new CCParentInfo(funcSymbNr, other.mCCParents, myInfo.mNext);
				myInfo = myInfo.mNext;
			}
			other = other.mNext;
		}
	}
	
	public void unmergeParentInfo(CCParentInfo other) {
		CCParentInfo myInfo = this;
		// skip head
		other = other.mNext;
		while (other != null) {
			int funcSymbNr = other.mFuncSymbNr;
			while (myInfo.mNext.mFuncSymbNr < funcSymbNr) {
				myInfo = myInfo.mNext;
			}
			assert (myInfo.mNext.mFuncSymbNr == funcSymbNr);
			if (myInfo.mNext.mCCParents == other.mCCParents) {
				/* remove info */
				myInfo.mNext = myInfo.mNext.mNext;
			} else {
				/* unjoin lists */
				myInfo = myInfo.mNext;
				myInfo.mCCParents.unjoinList(other.mCCParents);
			}
			other = other.mNext;
		}
	}

	public SimpleList<Parent> getParentInfo(int funcSymbNr) {
		CCParentInfo info = mNext;
		while (info != null && info.mFuncSymbNr < funcSymbNr)
			info = info.mNext;
		if (info != null && info.mFuncSymbNr == funcSymbNr)
			return info.mCCParents;
		return new SimpleList<Parent>();
	}

}
