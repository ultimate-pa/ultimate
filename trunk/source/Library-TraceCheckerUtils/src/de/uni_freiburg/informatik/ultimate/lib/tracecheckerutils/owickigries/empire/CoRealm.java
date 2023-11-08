package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.BranchingProcessToUltimateModel;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public final class CoRealm<PLACE,LETTER> {
	
	private final ICoRelation<LETTER, PLACE> mCoRelation;
	private final Realm<PLACE,LETTER> mRealm;
	private final Condition<LETTER,PLACE> mCondition;
	
	/**
	 * Subset of Realm's condition that are corelated to specified condition;
	 */
	private final Set<Condition<LETTER, PLACE>> mPosRealm;
	
	/**
	 * Subset of Realm's condition that are not corelated to mCondition;
	 */
	private final Set<Condition<LETTER,PLACE>> mNegRealm;
	
	/**
	 * Corelation type of condition wrt. Realm.
	 */
	private final CoRelationType mCoRel;
	
	
	public CoRealm(Realm<PLACE,LETTER> realm, Condition<LETTER,PLACE> condition, 
			BranchingProcess<LETTER,PLACE> bp) {
		mCoRelation = bp.getCoRelation();
		mRealm = realm;
		mCondition = condition;
		mPosRealm = getPosRealm();
		mNegRealm = DataStructureUtils.difference(mRealm.getConditions(), mPosRealm);
		mCoRel = getCoRelType(); 		
	}	
	
	/**
	 * @return Subset of Realm's conditions corelated to CoRealm' condition.
	 */
	private final Set<Condition<LETTER, PLACE>> getPosRealm(){
		return DataStructureUtils.intersection(mRealm.getConditions(), 
						mCoRelation.computeCoRelatatedConditions(mCondition)); 				
	}
	
	/**
	 * @return CoRelation type of Realm wrt. specified condition.
	 */
	
	private final CoRelationType getCoRelType() {
		if(mRealm.getConditions().equals(mPosRealm)) {
			return CoRelationType.POSITIVE;
		}
		else if(mRealm.getConditions().equals(mNegRealm)) {
			return CoRelationType.NEGATIVE;
		}
		else {
			return CoRelationType.PARTIAL;
		}
		
	}
	
	public final CoRelationType getCoRelation() {
		return mCoRel;
	}	

	 
}
