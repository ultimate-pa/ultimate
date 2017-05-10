package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner;

import java.util.Deque;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;

/**
 * Backbone of a LoopBody
 * 
 * @author Jonas Werner <jonaswerner95@gmail.com>
 *
 */

public class Backbone {

	private final Deque<IcfgEdge> mPath;
	private final TransFormula mFormula;
	private TermVariable mPathCounter;
	private TransFormula mCondition;
	private SymbolicMemory mSymbolicMemory;

	/**
	 * Construct a new backbone for a loop
	 * 
	 * @param path
	 *            The path of the backbone in the {@link IIcfg}.
	 * @param tf
	 *            The paths {@link TransFormula}.
	 */
	public Backbone(final Deque<IcfgEdge> path, final TransFormula tf) {
		mPath = path;
		mFormula = tf;
		mPathCounter = null;
		mCondition = null;
		mSymbolicMemory = null;
	}

	public void setPathCounter(TermVariable pathCounter) {
		mPathCounter = pathCounter;
	}

	/**
	 * set the backbone's entry condition.
	 * 
	 * @param condition
	 *            the backbone's condition.
	 */
	public void setCondition(TransFormula condition) {
		mCondition = condition;
	}

	public void setSymbolicMemory(SymbolicMemory memory) {
		mSymbolicMemory = memory;
	}

	/**
	 * Returns the path of the backbone.
	 * 
	 * @return the path of the backbone
	 */
	public Deque<IcfgEdge> getPath() {
		return mPath;
	}

	public TermVariable getPathCounter() {
		return mPathCounter;
	}

	/**
	 * Returns the {@link TransFormula} of the backbone.
	 * 
	 * @return
	 */
	public TransFormula getFormula() {
		return mFormula;
	}

	/**
	 * Returns the entry condition of the backbone.
	 */
	public TransFormula getCondition() {
		return mCondition;
	}

	public SymbolicMemory getSymbolicMemory() {
		return mSymbolicMemory;
	}

	@Override
	public String toString() {
		return mPath.toString();
	}

}
