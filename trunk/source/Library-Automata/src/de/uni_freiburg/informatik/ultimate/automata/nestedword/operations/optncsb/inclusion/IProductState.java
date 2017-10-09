package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion;

/**
 * only for Buchi automata
 * */
public interface IProductState {
	
	default boolean contentEq(IProductState other) {
		return getFstState() == other.getFstState()
				&& getSndState() == other.getSndState()
				&& getTrackNumber() == other.getTrackNumber();
	}
	
	int getFstState();
	
	int getSndState();
	
	TrackNumber getTrackNumber();
	
	/**
	 * current state is in TRACK_ONE
	     * If fst is final and the snd is not, then we jump to TRACK_TWO to wait snd to be final
	     * If fst and snd are both final, we already see final states in both operands, stay in track one
	 * current state is in TRACK_TWO: means that we already saw fst final before
	     * If snd is final, then we jump to TRACK_ONE to see fst final states
	     * if snd is not final, then we stay in TRACK_TWO
	 *    */
	default TrackNumber getSuccStateTrack(boolean fstAcc, boolean sndAcc) {
		
		TrackNumber succTrack;
		if (getTrackNumber().isOne()) {
			if (fstAcc && !sndAcc) {
				succTrack = TrackNumber.TRACK_TWO;
			} else {
				succTrack = TrackNumber.TRACK_ONE;
			}
		} else {
			assert getTrackNumber().isTwo();
			if (sndAcc) {
				succTrack = TrackNumber.TRACK_ONE;
			} else {
				succTrack = TrackNumber.TRACK_TWO;
			}
		}
		return succTrack;
	}
	
	TrackNumber getSuccStateTrack();

}
