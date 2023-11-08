package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.BranchingProcessToUltimateModel;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.Kingdom;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.KingdomLaw;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.Realm;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 * @param <LETTER>
 *            The type of statements in the Petri program
 */

public final class CoRook<PLACE, LETTER> {

	private final Rook<PLACE,LETTER> mRook;
	private final Condition<LETTER,PLACE> mCondition;
	private final CoKingdom<PLACE,LETTER> mCoKingdom;
	private final CoLaw<PLACE,LETTER> mCoLaw;
	private final ColonizationType mColonization;
	private final LegislationType mLegislation;
	private final boolean mIsColonizer;
	
	
	public CoRook(Condition<LETTER,PLACE> condition, Rook<PLACE,LETTER> rook,
			BranchingProcess<LETTER, PLACE> bp, boolean isColonizer) {
		mRook = rook;
		mCondition = condition;
		mIsColonizer = isColonizer;
		mCoKingdom = new CoKingdom<PLACE,LETTER>(mRook.getKingdom(), condition, bp);
		mCoLaw = new CoLaw<PLACE,LETTER>(mRook.getLaw(), condition, bp);
		mColonization = getColonizationStrategy();
		mLegislation = getLegislationStrategy();
	}
	
	private final ColonizationType getColonizationStrategy() {
		if (mIsColonizer)	{	
			if(mCoKingdom.getCoRelation() == CoRelationType.POSITIVE 
					&& mCoLaw.getCoRelation() == CoRelationType.POSITIVE) {
				return ColonizationType.EXPANSION;
			}
			else if(mCoKingdom.getCoRelation() == CoRelationType.PARTIAL
					&& mCoLaw.getCoRelation() == CoRelationType.POSITIVE) {
					if(mCoKingdom.getConflictFree()) {
						return ColonizationType.IMMIGRATION;
					}
					else {
						return ColonizationType.FOUNDATION;
					}
			}
			else {
				return ColonizationType.DEFEAT;
			}	
		}
		return ColonizationType.NULL;
	}
	
	private final LegislationType getLegislationStrategy() {
		if(!mIsColonizer) {
			if(mCoKingdom.getCoRelation() == CoRelationType.POSITIVE 
					&& mCoLaw.getCoRelation() == CoRelationType.POSITIVE) {
				return LegislationType.APPROVAL;
			}
			else if(mCoKingdom.getCoRelation() == CoRelationType.POSITIVE
					&& mCoLaw.getCoRelation() == CoRelationType.PARTIAL) {
				return LegislationType.ENACTMENT;
			}
			else if(mCoKingdom.getCoRelation() == CoRelationType.PARTIAL
					&& mCoLaw.getCoRelation() == CoRelationType.POSITIVE) {
				return LegislationType.RATIFICATION;
			}
			else {
				return LegislationType.REJECTION;
			}
		}
		return LegislationType.NULL; 
	}
	
	public LegislationType getLegislation() {
		return mLegislation;
	}
	
	public ColonizationType getColonization() {
		return mColonization;
	}
	
	public Rook<PLACE,LETTER> getRook(){
		return mRook;
	}
	
	public Condition<LETTER,PLACE> getCondition(){
		return mCondition;
	}
	
	public CoKingdom<PLACE,LETTER> getCoKingdom(){
		return mCoKingdom;
	}
	
	public CoLaw<PLACE,LETTER> getCoLaw(){
		return mCoLaw;
	}
}
