package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.BranchingProcessToUltimateModel;
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

public final class Crown<PLACE, LETTER> {
	
	private final Set<Rook<PLACE,LETTER>> mCrown;
	
	private  final BranchingProcess<LETTER, PLACE> mBp; 
	
	public Crown(BranchingProcess<LETTER, PLACE> bp){
		mBp = bp;
		mCrown = new HashSet<Rook<PLACE, LETTER>>();
	}
	
	public Set<Rook<PLACE,LETTER>> getRooks(){
		return mCrown;
	}
	
	public void addRook(Rook<PLACE,LETTER> rook) {
		mCrown.add(rook);
	}
	
	public void addRook(Set<Rook<PLACE,LETTER>> rooks) {
		mCrown.addAll(rooks);
	}
	
	public boolean removeRook(Rook<PLACE,LETTER> rook) {
		if(mCrown.contains(rook)) {
			mCrown.remove(rook);
			return true;
		}
		return false;
	}
	
	public boolean removeRook(Set<Rook<PLACE,LETTER>> rooks) {
		if(mCrown.containsAll(rooks)) {
			mCrown.removeAll(rooks);
			return true;
		}
		return false;
	}
	
}
