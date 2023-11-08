package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.BranchingProcessToUltimateModel;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public final class CoKingdom<PLACE,LETTER> {
	
	
	private final ICoRelation<LETTER, PLACE> mCoRelation;
	private final Kingdom<PLACE,LETTER> mKingdom;
	private final Condition<LETTER,PLACE> mCondition;
	
	/**
	 * Subset of Realms in Kingdom that have positive 
	 * corelation wrt. specified condition;
	 */
	public  Set<Realm<PLACE,LETTER>> mPosKingdom;
	
	/**
	 * Subset of Realms in Kingdom that have partial 
	 * corelation wrt. specified condition;
	 */
	public Set<Realm<PLACE,LETTER>> mParKingdom;
	
	/**
	 * Subset of Realms in Kigmdom that are have negative 
	 * corelation wrt. specified condition
	 */
	public  Set<Realm<PLACE,LETTER>> mNegKingdom;
	
	/**
	 * Corelation type of condition wrt. Realm.
	 */
	private final CoRelationType mCoRel;
	
	private final boolean mConflictFree;
	
	public CoKingdom(Kingdom<PLACE,LETTER> kingdom, Condition<LETTER,PLACE> condition, 
			BranchingProcess<LETTER,PLACE> bp) {
		mCoRelation = bp.getCoRelation();
		mKingdom = kingdom;
		mCondition = condition;
		getCoKingdoms(bp);
		mCoRel = getCoRelType(); 
		mConflictFree = getConflictFreedom(); //TODO: complete conflict freedom computation
	}
		
	/**
	 * Divide all Realms in Kingdom according to their realm corelation type.
	 * @param bp
	 */
	private final void getCoKingdoms(BranchingProcess<LETTER,PLACE> bp){
		for(Realm<PLACE,LETTER> realm: mKingdom.getRealms()) {
			CoRealm<PLACE,LETTER> coRealm = new CoRealm(realm,mCondition,bp);
			switch(coRealm.getCoRelation()) {
				case POSITIVE:
					mPosKingdom.add(realm);
					break;
				case NEGATIVE:
					mNegKingdom.add(realm);
					break;
				default:
					mParKingdom.add(realm);								
			} 
		}
	}
	
	/**
	 * @return CoRelation type pf Kingdom according
	 * to the corelation time of the kingdom's realms.
	 */
	private final CoRelationType getCoRelType() {
		if(mKingdom.equals(mPosKingdom)) {
			return CoRelationType.POSITIVE;
		}	
		else if(mNegKingdom.size() == 1 && 
				mPosKingdom.containsAll(DataStructureUtils.difference
						(mKingdom.getRealms(), mNegKingdom))){
			return CoRelationType.PARTIAL;				
		}
		else if(mParKingdom.size() == 1 && 
				mPosKingdom.containsAll(DataStructureUtils.difference
						(mKingdom.getRealms(), mParKingdom))){
			return CoRelationType.DIVERGENT;				
		}
		else {
			return CoRelationType.NEGATIVE;
		}
	}
	 public final CoRelationType getCoRelation() {
		 return mCoRel;
	 }
	 
	 private final boolean getConflictFreedom() {
			return true;
	}
	
	public boolean getConflictFree() {
		return mConflictFree;
	}	

	public Set<Realm<PLACE,LETTER>> getNegKingdom(){
		return mNegKingdom;
	}
	
	public Set<Realm<PLACE,LETTER>> getPosKingdom(){
		return mPosKingdom;
	}
}
