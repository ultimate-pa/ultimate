package de.uni_freiburg.informatik.ultimate.automata.dynamic_stratified_reduction;

import java.util.HashSet;
import java.util.Set;




/* The abstraction levels for DynamicStratifiedReduction
 * 
 * 
 * 
 */

class AbstractionLevel<L> {
	public HashSet<L> mValue;
	public boolean mLocked;
	
	
	
	public AbstractionLevel(HashSet<L> protectedVar, boolean defined){
		mValue = protectedVar;
		mLocked = defined;
	}
	
	public static AbstractionLevel createEmpty(){
		return new AbstractionLevel(new HashSet(), false);
	}

	public void addToAbstractionLevel (Set<L> vars) {
		this.mValue.addAll(vars);
	}
	
	
	public boolean isEqual(AbstractionLevel<L> level) {
	//return true if the two sets of variables are the same
		//assert (this.alreadyDefined() && level.alreadyDefined()): "Only fully defined abstraction levels can be compared for equality";
		return this.getValue().equals(level.getValue());
	}
	
	public boolean isLEQ(AbstractionLevel<L> level) {
	/* return true if the second set is a subset of the first, i.e. if the abstraction level of the first argument is  less or equal than the second set's level.
		If the 1st abstraction level is not completly defined but already a superset of the 2nd abstraction level that's ok */
		assert (level.isLocked()): "Second abstraction level is not yet defined"; 
		return this.getValue().containsAll(level.getValue());
	}
	
	
	public HashSet<L> getValue() {
	// return the set of protected variables constituting the abstraction's abstraction level
		return this.mValue;
	}

	public boolean isLocked() {
		// return whether the abstraction level has already been assigned all corresponding variables
		return this.mLocked;
	}
}