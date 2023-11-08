package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.BranchingProcessToUltimateModel;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.CoRealm;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;


public final class Realm<PLACE, LETTER>{
	/**
	 * The set of conditions in realm.
	 */
	private final Set<Condition<LETTER, PLACE>> mRealm;
	
	public Realm(Set<Condition<LETTER,PLACE>> realm) {
		mRealm = realm;
	}
	
	/**
	 * @return set of all conditions in region.
	 */
	public Set<Condition<LETTER,PLACE>> getConditions(){
		return mRealm;
	}
	
	/**
	 * * Adds the specified condition into the set of conditions in the realm.
	 * @param condition 
	 */
	public void addCondition(Condition<LETTER,PLACE> condition) {
		mRealm.add(condition);
	}
	
	/**
	 * Add the specified set of conditions to the realm.
	 * @param conditions
	 */
	public void addCondition(Set<Condition<LETTER, PLACE>>conditions) {
		mRealm.addAll(conditions);
	}
	
	/**
	 * Removes the specified condition from the realm.
	 * @param condition
	 */
	public void removeCondition(Condition<PLACE, LETTER> condition) {
		if (mRealm.contains(condition)){ 
			mRealm.remove(condition);
		}
	}
	
	/**
	 * @param bp  branching process over which corelation is checked.
	 * @return true if condition is NOT corelated to all conditions in the region.
	 * TODO: itself?? / intersection or isCorelated foreach condition in realm??
	 */
	public boolean checkAddCorelation(Condition<LETTER, PLACE> condition, BranchingProcess<LETTER, PLACE> bp) {
		ICoRelation<LETTER, PLACE> coRelation = bp.getCoRelation();
		//set of conditions in Branching process to which the specified condition is corelated with.
		Set<Condition<LETTER, PLACE>> coConditions = coRelation.computeCoRelatatedConditions(condition);
		//if the intersection of the coCondition and the realm is empty then the condition is not corelated
		//to any of the conditions in the realm and hence can be added.
		if(DataStructureUtils.haveEmptyIntersection(coConditions, mRealm)) {
			return true;
		}
		else {
			return false;	
		}
		
	}
	
	/**
	 * @param bp  branching process over which corelation is checked.
	 * @return true if condition is corelated to all conditions in the region.
	 * For the addition of a condition into a territory. 
	 * True AddCorelation to the realm in which the conditionn is added and true checkCorelation to all other realms.
	 * TODO: itself?? / intersection or isCorelated foreach condition in realm??
	 */
	public boolean checkCorelation(Condition<LETTER, PLACE> condition, BranchingProcess<LETTER, PLACE> bp) {
		ICoRelation<LETTER, PLACE> coRelation = bp.getCoRelation();
		//set of conditions in Branching process to which the specified condition is corelated with.
		Set<Condition<LETTER, PLACE>> coConditions = coRelation.computeCoRelatatedConditions(condition);
		//if the intersection of the coCondition and the realm is empty then the condition is not corelated
		//to any of the conditions in the realm and hence can be added.
		if(coConditions.containsAll(mRealm)) {
			return true;
		}
		else {
			return false;	
		}
	}
	
	/**
	 * @param condition
	 * @param bp
	 * @return CoRealm with CoRelationType, Positive and Negative corelated conditions.
	 */
	public CoRealm<PLACE,LETTER> getCoRealm(Condition<LETTER, PLACE> condition, 
			BranchingProcess<LETTER, PLACE> bp) {
		return new CoRealm<PLACE,LETTER>(this, condition, bp);
	}

	
	
	
	
	
	
	
	
}
