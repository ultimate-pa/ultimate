/*
 * Copyright (C) 2017 Jonas Werner (jonaswerner95@gmail.com)
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * A Loop
 *
 * @author Jonas Werner (jonaswerner95@gmail.com)
 */

public class Loop {

	private Deque<IcfgEdge> mPath;
	private Deque<Backbone> mBackbones;
	private final IcfgLocation mLoopHead;
	private Term mTerm;
	private Term mCondition;
	private IteratedSymbolicMemory mIteratedMemory;
	private List<TermVariable> mAuxVars;
	private Map<IcfgLocation, Backbone> mErrorPaths;
	private Boolean mHasNestedLoops;
	private Deque<Loop> mNestedLoops;
	private Boolean mIsSummarized;
	private Map<IProgramVar, TermVariable> mInVars;
	private Map<IProgramVar, TermVariable> mOutVars;
	private UnmodifiableTransFormula mAcceleratedCondition;
	private IcfgEdge mLoopExit;

	/**
	 * Construct a new loop.
	 * 
	 * @param loopHead
	 *            The loop entry node.
	 */
	public Loop(final IcfgLocation loopHead) {
		mPath = null;
		mLoopHead = loopHead;
		mBackbones = new ArrayDeque<>();
		mCondition = null;
		mIteratedMemory = null;
		mAuxVars = new ArrayList<>();
		mErrorPaths = new HashMap<>();
		mHasNestedLoops = false;
		mIsSummarized = false;
		mNestedLoops = new ArrayDeque<>();
		mInVars = new HashMap<>();
		mOutVars = new HashMap<>();
		mAcceleratedCondition = null;
		mLoopExit = null;
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

	public Map<IcfgLocation, Backbone> getErrorPaths() {
		return mErrorPaths;
	}

	public IteratedSymbolicMemory getIteratedMemory() {
		return mIteratedMemory;
	}

	public Term getTerm() {
		return mTerm;
	}

	public List<TermVariable> getVars() {
		return mAuxVars;
	}

	public Map<IProgramVar, TermVariable> getInVars() {
		return mInVars;
	}

	public Map<IProgramVar, TermVariable> getOutVars() {
		return mOutVars;
	}

	public IcfgEdge getLoopExit() {
		return mLoopExit;
	}

	/**
	 * Get the loophead as IcfgLocation
	 */
	public IcfgLocation getLoophead() {
		return mLoopHead;
	}

	public Deque<Loop> getNestedLoops() {
		return mNestedLoops;
	}

	public UnmodifiableTransFormula getAcceleratedCondition() {
		return mAcceleratedCondition;
	}

	public void setPath(final Deque<IcfgEdge> path) {
		mPath = path;
	}

	public void setLoopExit(final IcfgEdge loopExit) {
		mLoopExit = loopExit;
	}

	/**
	 * If there is an Assertion in the Loop, add it here
	 * 
	 * @param errorLocation
	 *            The Error {@link IcfgLocation}
	 * 
	 * @param errorPath
	 *            The Errorpath in form of a {@link Backbone}
	 */
	public void addErrorPath(final IcfgLocation errorLocation, final Backbone errorPath) {
		mErrorPaths.put(errorLocation, errorPath);
	}

	/**
	 * attach a nested loop
	 * 
	 * @param loop
	 *            the nested loop
	 */
	public void addNestedLoop(final Loop loop) {
		mNestedLoops.addLast(loop);
	}

	/**
	 * public void setFormula(final TransFormula tf) { mFormula = tf; mInVars =
	 * tf.getInVars(); mOutVars = tf.getOutVars(); }
	 */

	public void setCondition(final Term condition) {
		mCondition = condition;
	}

	public void setInVars(final Map<IProgramVar, TermVariable> inVars) {
		mInVars = inVars;
	}

	public void setOutVars(final Map<IProgramVar, TermVariable> outVars) {
		mOutVars = outVars;
	}

	public void setIteratedSymbolicMemory(final IteratedSymbolicMemory memory) {
		mIteratedMemory = memory;
	}

	public void setAcceleratedCondition(final UnmodifiableTransFormula condition) {
		mAcceleratedCondition = condition;
	}

	public Boolean isNested() {
		return mHasNestedLoops;
	}

	public Boolean isSummarized() {
		return mIsSummarized;
	}

	/**
	 * The Loop has nested Loops
	 */
	public void setNested() {
		mHasNestedLoops = true;
	}

	public void setTerm(Term term) {
		mTerm = term;
	}

	/**
	 * The loop has been summarized, there is a {@link IteratedSymbolicMemory}
	 */
	public void setSummarized() {
		mIsSummarized = true;
	}

	/**
	 * add a var
	 * 
	 * @param vars
	 *            aux vars
	 */
	public void addVar(final List<TermVariable> vars) {
		mAuxVars.addAll(vars);
	}

	@Override
	public String toString() {
		return mPath.toString();
	}

	/**
	 * Get the {@link Backbone}s as human readable Text.
	 * 
	 * @return String representation of the backbone path
	 */
	public String backbonesToString() {
		StringBuilder str = new StringBuilder();
		for (Backbone backbone : mBackbones) {
			str.append(backbone.toString());
		}
		return str.toString();
	}

}
