package de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * Class that represents a ICFG component of a HybridAutomata component. It is used for the translation from
 * HybridAutomaton to ICFG
 * 
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 *
 */
public class HybridCfgComponent {
	
	private final String mId;
	private final IcfgLocation mStartLocation;
	private final IcfgLocation mEndLocation;
	private final List<IcfgLocation> mLocations;
	private final List<IcfgInternalTransition> mTransitions;
	
	public HybridCfgComponent(String string, IcfgLocation start, IcfgLocation end, List<IcfgLocation> locations,
			List<IcfgInternalTransition> transitions) {
		mId = string;
		mStartLocation = start;
		mEndLocation = end;
		mLocations = locations;
		mTransitions = transitions;
	}
	
	public String getId() {
		return mId;
	}
	
	public IcfgLocation getStart() {
		return mStartLocation;
	}
	
	public IcfgLocation getEnd() {
		return mEndLocation;
	}
	
	public List<IcfgLocation> getLocations() {
		return mLocations;
	}
	
	public List<IcfgInternalTransition> getTransitions() {
		return mTransitions;
	}
	
}
