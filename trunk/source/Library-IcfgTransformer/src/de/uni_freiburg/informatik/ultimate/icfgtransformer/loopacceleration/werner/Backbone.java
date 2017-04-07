package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner;

import java.util.Deque;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;

/**
 * Backbone of a LoopBody
 * @author Jonas Werner <jonaswerner95@gmail.com>
 *
 */

public class Backbone {
	
	private final Deque<IcfgEdge> mPath;
	private final Term mCondition;
	
	public Backbone(final Deque<IcfgEdge> path) {
		mPath = path;
		mCondition = null;
	}
	
	/**
	 * Returns the path of the Backbone
	 */
	public Deque<IcfgEdge> getPath() {
		return mPath;
	}
	
	@Override
	public String toString() {
		return mPath.toString();
	}
	
}
