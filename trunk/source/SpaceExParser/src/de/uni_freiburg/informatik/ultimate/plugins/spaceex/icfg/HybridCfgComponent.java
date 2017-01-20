package de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;

/**
 * Class that represents a ICFG component of a HybridAutomata component. It is used for the translation from
 * HybridAutomaton to ICFG
 * 
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 *
 */
public class HybridCfgComponent {
	
	private final String mId;
	private final BoogieIcfgLocation mStartLocation;
	private final BoogieIcfgLocation mEndLocation;
	private final List<BoogieIcfgLocation> mLocations;
	private final List<IcfgInternalTransition> mTransitions;
	
	public HybridCfgComponent(String string, BoogieIcfgLocation start, BoogieIcfgLocation end,
			List<BoogieIcfgLocation> locations, List<IcfgInternalTransition> transitions) {
		mId = string;
		mStartLocation = start;
		mEndLocation = end;
		mLocations = locations;
		mTransitions = transitions;
	}
	
	public String getId() {
		return mId;
	}
	
	public BoogieIcfgLocation getStart() {
		return mStartLocation;
	}
	
	public BoogieIcfgLocation getEnd() {
		return mEndLocation;
	}
	
	public List<BoogieIcfgLocation> getLocations() {
		return mLocations;
	}
	
	public List<IcfgInternalTransition> getTransitions() {
		return mTransitions;
	}
	
	@Override
	public String toString() {
		String comp = "\n";
		String indent = "   ";
		comp += "ID: " + mId + "\n";
		comp += "Start: " + mStartLocation.getDebugIdentifier() + "\n";
		for (IcfgEdge trans : mStartLocation.getOutgoingEdges()) {
			comp += indent + "** outgoing:" + "(" + trans.getSource().getDebugIdentifier() + "-->"
					+ trans.getTarget().getDebugIdentifier() + ")\n";
		}
		for (IcfgEdge trans : mStartLocation.getIncomingEdges()) {
			comp += indent + "** incoming:" + "(" + trans.getSource().getDebugIdentifier() + "-->"
					+ trans.getTarget().getDebugIdentifier() + ")\n";
		}
		comp += "End: " + mEndLocation.getDebugIdentifier() + "\n";
		for (IcfgEdge trans : mEndLocation.getOutgoingEdges()) {
			comp += indent + "** outgoing:" + "(" + trans.getSource().getDebugIdentifier() + "-->"
					+ trans.getTarget().getDebugIdentifier() + ")\n";
		}
		for (IcfgEdge trans : mEndLocation.getIncomingEdges()) {
			comp += indent + "** incoming:" + "(" + trans.getSource().getDebugIdentifier() + "-->"
					+ trans.getTarget().getDebugIdentifier() + ")\n";
		}
		comp += "locations: \n";
		for (BoogieIcfgLocation icfgLocation : mLocations) {
			comp += indent + "* Loc:" + icfgLocation.getDebugIdentifier() + "\n";
			for (IcfgEdge trans : icfgLocation.getOutgoingEdges()) {
				comp += indent + "** outgoing:" + "(" + trans.getSource().getDebugIdentifier() + "-->"
						+ trans.getTarget().getDebugIdentifier() + ")\n";
			}
			for (IcfgEdge trans : icfgLocation.getIncomingEdges()) {
				comp += indent + "** incoming:" + "(" + trans.getSource().getDebugIdentifier() + "-->"
						+ trans.getTarget().getDebugIdentifier() + ")\n";
			}
		}
		comp += "transitions: \n";
		for (IcfgInternalTransition trans : mTransitions) {
			comp += indent + "* (" + trans.getSource().getDebugIdentifier() + "-->"
					+ trans.getTarget().getDebugIdentifier() + ")\n";
		}
		return comp;
	}
}
