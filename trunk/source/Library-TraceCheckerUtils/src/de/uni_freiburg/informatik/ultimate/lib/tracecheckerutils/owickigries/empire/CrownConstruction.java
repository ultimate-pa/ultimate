package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.BranchingProcessToUltimateModel;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.Crown;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.KingdomLaw;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.Realm;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.Rook;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 * @param <LETTER>
 *            The type of statements in the Petri program
 */
public final class CrownConstruction <PLACE, LETTER> {
	
	private final BranchingProcess<LETTER, PLACE> mBp;
	
	private final Crown<PLACE, LETTER> mCrown;
	
	private final Crown<PLACE, LETTER> mPreCrown;
	
	private final Set<Condition<LETTER,PLACE>> mOrigConds;
	
	private final Set<Condition<LETTER,PLACE>> mAssertConds;
	
	//TODO: add original and assertion conditions sets variables
	
	public CrownConstruction(BranchingProcess<LETTER, PLACE> bp, 
			Set<Condition<LETTER,PLACE>> origConds, Set<Condition<LETTER,PLACE>> assertConds) {
		mBp = bp;
		mCrown = new Crown<PLACE, LETTER>(mBp);
		mPreCrown = new Crown<PLACE, LETTER>(mBp);
		mOrigConds = origConds; 
		mAssertConds = assertConds;
		//TODO: Check/ensure that the sets are disjoint
		//settlements
		//colonization
		//legislation
		//Kindred search and cleaning
	}
	
	private void settlements() {
		//Create a new rook for each original condition.
		//Add a to crown a new rook with "capital" and one corelated assertion condition
	}
	
	
	private void colonization() {
		//TODO: for each original condition colonize(condition....)
	}
	
	private boolean colonize(Condition<LETTER,PLACE> condition, Rook<PLACE,LETTER> rook) {
		boolean colonizer = isColonizer(condition);
		if (colonizer) {//TODO: ensure that condition is colonizer.
			CoRook<PLACE,LETTER> coRook = new CoRook<PLACE,LETTER>
										(condition, rook, mBp, colonizer);
			switch(coRook.getColonization()) {
				case  EXPANSION:
					break;
				case IMMIGRATION:
					break;
				case FOUNDATION:
					break;
				default:	
	
				break;
			}
			return true;
			//Call respective expansion strategy
			//TODO: Next is to define the series of expansion strategies, 
			///new and modification to existing one with CoROok as parameter.
		}
		return false;
	}
	
	private boolean legislate(Condition<LETTER,PLACE> condition, Rook<PLACE,LETTER> rook) {
		boolean colonizer = isColonizer(condition);
		if (!colonizer) {//TODO: ensure that condition is not colonizer
			CoRook<PLACE,LETTER> coRook = new CoRook<PLACE,LETTER>
										(condition, rook, mBp, colonizer);
			switch(coRook.getLegislation()) {
				case APPROVAL:
					break;
				case ENACTMENT:
					break;
				case RATIFICATION:
					break;
				default:
					break;	
			}
			return true;
	}
		return false;
	}
	
	
	//TODO: depends on how the conditions types are computed at the end
	private boolean isColonizer(Condition<LETTER,PLACE> condition){
		return mOrigConds.contains(condition);
	}
	
	private void expand(CoRook<PLACE,LETTER> coRook) {
		mCrown.removeRook(coRook.getRook());
		Rook<PLACE,LETTER> rook = coRook.getRook();
		rook.expansion(coRook.getCondition());
		mCrown.addRook(rook);
	}
	
	private void immigrate(CoRook<PLACE,LETTER> coRook) {
		mCrown.removeRook(coRook.getRook());
		Rook<PLACE,LETTER> rook = coRook.getRook();
		rook.immigration(coRook.getCondition(), getNegKingdom(coRook));
		mCrown.addRook(rook);
	}
	
	private void founding(CoRook<PLACE,LETTER> coRook) {
		Rook<PLACE,LETTER> rook = coRook.getRook();
		Set<Realm<PLACE,LETTER>> newRealms = rook.getKingdom().getRealms();
		newRealms.remove(getNegKingdom(coRook));	
		//TODO: newRealm = conflict free realm + condition 
		//TODO:Add new Realm to newRealms
		Kingdom<PLACE,LETTER> kingdom = new Kingdom<PLACE,LETTER>(newRealms);		
		mCrown.addRook(new Rook<PLACE,LETTER>(kingdom,rook.getLaw()));
	}
	
	private void approve(CoRook<PLACE,LETTER> coRook) {
		mCrown.removeRook(coRook.getRook());
		Rook<PLACE,LETTER> rook = coRook.getRook();
		rook.approval(coRook.getCondition());
		mCrown.addRook(rook);		
	}
	
	private void enactment(CoRook<PLACE,LETTER> coRook) {
		Rook<PLACE,LETTER> rook = coRook.getRook();
		Kingdom<PLACE,LETTER> kingdom = new Kingdom<PLACE,LETTER>
										(coRook.getCoKingdom().getPosKingdom());
		KingdomLaw<PLACE,LETTER> law = new KingdomLaw<PLACE,LETTER>
										(new HashSet<Condition<LETTER,PLACE>>());
		law.addCondition(coRook.getCondition());
		mCrown.addRook(new Rook<PLACE,LETTER>(kingdom, law));
	}
	
	private void ratify(CoRook<PLACE,LETTER> coRook){
		KingdomLaw<PLACE,LETTER> law = new KingdomLaw<PLACE,LETTER>
									    (new HashSet<Condition<LETTER,PLACE>>());
		law.addCondition(coRook.getCondition());
		mCrown.addRook(new Rook<PLACE,LETTER>(coRook.getRook().getKingdom(), law));
	}

	private Realm<PLACE,LETTER> getNegKingdom(CoRook<PLACE,LETTER> coRook){
		return coRook.getCoKingdom().getNegKingdom().iterator().next();		
	}
	
}









