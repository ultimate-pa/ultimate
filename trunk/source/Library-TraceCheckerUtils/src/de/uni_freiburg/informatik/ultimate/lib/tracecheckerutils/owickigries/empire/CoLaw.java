package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.BranchingProcessToUltimateModel;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public final class CoLaw<PLACE,LETTER> {

	private final ICoRelation<LETTER,PLACE> mCoRelation;
	private final KingdomLaw<PLACE, LETTER> mLaw;
	private final Condition<LETTER,PLACE> mCondition;
	
	/**
	 * Subset of Law's condition that are corelated to specified condition;
	 */
	private final Set<Condition<LETTER, PLACE>> mPosLaw;
	
	/**
	 * Subset of Law's condition that are not corelated to mCondition;
	 */
	private final Set<Condition<LETTER,PLACE>> mNegLaw;
	
	/**
	 * Corelation type of condition wrt. Law.
	 */
	private final CoRelationType mCoRel;
	
	//TODO: keep both classes (CoRealm and CoLaw) or merge into one?
	//		issue: neg & partial corelationtype conflict.(one for each?)
	public CoLaw(KingdomLaw<PLACE,LETTER> law, Condition<LETTER, PLACE> condition, 
			BranchingProcess<LETTER,PLACE> bp) {
		mCoRelation = bp.getCoRelation();
		mLaw = law;
		mCondition = condition;
		mPosLaw = getPosLaw();
		mNegLaw = DataStructureUtils.difference(mLaw.getConditions(), mPosLaw);
		mCoRel = getCoRelType();		
	}
	
	/**
	 * @return Subset of Law's conditions corelated to CoLaw's condition.
	 */
	private final Set<Condition<LETTER,PLACE>> getPosLaw(){
		return DataStructureUtils.intersection(mLaw.getConditions(), 
				mCoRelation.computeCoRelatatedConditions(mCondition)); 			
	}
	
	/**
	 * @return CoRelation type of Law wrt. specified condition.
	 */
	private final CoRelationType getCoRelType() {
		if(mLaw.getConditions().equals(mPosLaw)) {
			return CoRelationType.POSITIVE;
		}
		else if(mNegLaw.size() == 1) {
			return CoRelationType.PARTIAL;
		}
		else {
			return CoRelationType.NEGATIVE;
		}
	}
	
	public CoRelationType getCoRelation() {
		return mCoRel;
	}
}
