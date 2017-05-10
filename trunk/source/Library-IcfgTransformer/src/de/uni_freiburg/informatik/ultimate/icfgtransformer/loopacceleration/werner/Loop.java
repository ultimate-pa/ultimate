package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner;

import java.util.ArrayDeque;
import java.util.Deque;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;

/**
 * A Loop
 *
 * @author Jonas Werner (jonaswerner95@gmail.com)
 */

public class Loop {

	private final Deque<IcfgEdge> mPath;
	private Deque<Backbone> mBackbones;
	private final IcfgLocation mLoopHead;
	private final TransFormula mFormula;
	private Term mCondition;
	private IteratedSymbolicMemory mIteratedMemory;

	/**
	 * Construct a new loop.
	 * 
	 * @param path
	 *            The loop's path in the ICFG.
	 * 
	 * @param loopHead
	 *            The loop entry node.
	 * @param tf
	 *            the loops {@link TransFormula}
	 */
	public Loop(final Deque<IcfgEdge> path, final IcfgLocation loopHead, final TransFormula tf) {
		mPath = path;
		mLoopHead = loopHead;
		mBackbones = new ArrayDeque<>();
		mFormula = tf;
		mCondition = null;
		mIteratedMemory = null;
	}

	/**
	 * Add a new backbone to the loop.
	 * 
	 * @param backbone
	 *            The backbone to be assigned to the loop.
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

	public TransFormula getFormula() {
		return mFormula;
	}

	/**
	 * Get the loops backbones as IcfgEdges
	 */
	public Deque<Backbone> getBackbones() {
		return mBackbones;
	}

	/**
	 * Get the loops looping condition.
	 */
	public Term getCondition() {
		return mCondition;
	}

	public IteratedSymbolicMemory getIteratedMemory() {
		return mIteratedMemory;
	}

	/**
	 * Get the loophead as IcfgLocation
	 */
	public IcfgLocation getLoophead() {
		return mLoopHead;
	}

	public void setCondition(Term condition) {
		mCondition = condition;
	}

	public void setIteratedSymbolicMemory(IteratedSymbolicMemory memory) {
		mIteratedMemory = memory;
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
