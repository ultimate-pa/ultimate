package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner;

import java.util.ArrayDeque;
import java.util.Deque;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * A Loop
 *
 * @author Jonas Werner (jonaswerner95@gmail.com)
 */

public class Loop {
	
	private final Deque<IcfgEdge> mPath;
	private Deque<Backbone> mBackbones;
	private final IcfgLocation mLoopHead;
	private final Term mCondition;
	
	public Loop(final Deque<IcfgEdge> path, final IcfgLocation loopHead) {
		mPath = path;
		mLoopHead = loopHead;
		mBackbones = new ArrayDeque<>();
		mCondition = null;
	}
	
	/**
	 * Add a new backbone to the loop.
	 */
	public void addBackbone(final Backbone backbone) {
		mBackbones.addLast(backbone);
	}
	
	/**
	 * Get loop path as IcfgEdges
	 */
	public Deque<IcfgEdge> getPath() {
		return mPath;
	}
	
	/**
	 * Get the loops backbones as IcfgEdges
	 */
	public Deque<Backbone> getBackbones() {
		return mBackbones;
	}
	
	/**
	 * Get the loophead as IcfgLocation
	 */
	public IcfgLocation getLoophead() {
		return mLoopHead;
	}
	
	@Override
	public String toString() {
		return mPath.toString();
	}
	
	public String backbonesToString() {
		StringBuilder str = new StringBuilder();
		for (Backbone backbone : mBackbones) {
			str.append(backbone.toString());
		}
		return str.toString();
	}

}
