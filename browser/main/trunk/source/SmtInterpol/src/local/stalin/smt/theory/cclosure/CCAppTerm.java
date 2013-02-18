package local.stalin.smt.theory.cclosure;

import local.stalin.smt.dpll.SimpleListable;

public class CCAppTerm extends CCTerm {
	CCTerm func, arg;
	int lastFormula, firstFormula;
	Parent leftParInfo, rightParInfo;
	
	class Parent extends SimpleListable<Parent> {
		CCAppTerm getData() {
			return CCAppTerm.this;
		}
		public String toString() {
			return CCAppTerm.this.toString();
		}
	}
	
	/**
	 * Constructor for CCAppTerms that are not permanently stored in the CC graph
	 */
	public CCAppTerm(CCTerm func, CCTerm arg) {
		 super();
		 this.func = func;
		 this.arg = arg;
	}

	public CCAppTerm(boolean isFunc, int numArgs, CCTerm func, CCTerm arg) {
		super(isFunc, numArgs);
		this.func = func;
		this.arg = arg;
		firstFormula = Integer.MAX_VALUE; lastFormula = -1;
		leftParInfo = new Parent();
		rightParInfo = new Parent();
		
		func.addParentInfo(0, leftParInfo);
		arg.addParentInfo(func.parentPosition, rightParInfo);
	}
	
	public void unlinkParentInfos() {
		leftParInfo.unlink();
		rightParInfo.unlink();
	}
	
	public void relinkParentInfos() {
		rightParInfo.relink();
		leftParInfo.relink();
	}
	
	public int getFirstFormula() {
		return firstFormula;
	}
	
	public int getLastFormula() {
		return lastFormula;
	}
	
	public void occursIn(int formulaNr) {
		func.occursIn(formulaNr);
		arg.occursIn(formulaNr);
		if (formulaNr < firstFormula)
			firstFormula = formulaNr;
		if (formulaNr > lastFormula)
			lastFormula = formulaNr;
	}
	
	public void toStringHelper(StringBuilder sb) {
		if (func instanceof CCAppTerm) {
			((CCAppTerm)func).toStringHelper(sb);
			sb.append(",");
		} else {
			sb.append(func).append("(");
		}
		sb.append(arg);
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		toStringHelper(sb);
		sb.append(")");
		return sb.toString();
	}
}
