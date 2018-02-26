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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

/**
 * Backbone of a LoopBody
 *
 * @author Jonas Werner <jonaswerner95@gmail.com>
 *
 */
public class Backbone {

	private final Deque<IcfgEdge> mPath;
	private final Deque<IcfgLocation> mNodes;
	private final List<IcfgLocation> mNestedLoops;
	private TransFormula mFormula;
	private TermVariable mPathCounter;
	private UnmodifiableTransFormula mCondition;
	private SymbolicMemory mSymbolicMemory;
	private Term mAbstractPathCondition;
	private Boolean mIsNested;

	/**
	 * Construct a new backbone for a loop
	 *
	 * @param path
	 *            The path of the backbone in the {@link IIcfg}.
	 * @param tf
	 *            The paths {@link TransFormula}.
	 * 
	 * @param isNested
	 *            does the backbone contain other loopheads
	 * 
	 * @param nestedLoops
	 *            Nested loops in the backbone
	 * 
	 */

	/**
	 * Construct a new backbone
	 * 
	 * @param trans
	 *            entry transition
	 */
	public Backbone(final IcfgEdge trans) {
		mPath = new ArrayDeque<>();
		mPath.addLast(trans);
		mNodes = new ArrayDeque<>();
		mNodes.add(trans.getSource());

		mFormula = null;
		mPathCounter = null;
		mCondition = null;
		mSymbolicMemory = null;
		mNestedLoops = new ArrayList<>();

		mIsNested = false;

		mAbstractPathCondition = null;
	}

	/**
	 * Copy a backbone
	 * 
	 * @param source
	 *            the original backbone.s
	 */
	public Backbone(final Backbone source) {
		mPath = new ArrayDeque<>(source.getPath());

		mNodes = new ArrayDeque<>(source.getNodes());

		mFormula = null;
		mPathCounter = null;
		mCondition = null;
		mSymbolicMemory = null;
		mNestedLoops = new ArrayList<>();

		mIsNested = false;

		mAbstractPathCondition = null;
	}

	/**
	 * attach a pathcounter to backbone.
	 * 
	 * @param pathCounter
	 */
	public void setPathCounter(final TermVariable pathCounter) {
		mPathCounter = pathCounter;
	}

	/**
	 * set the backbone's entry condition.
	 *
	 * @param condition
	 *            the backbone's condition.
	 */
	public void setCondition(final UnmodifiableTransFormula condition) {
		mCondition = condition;
	}

	/**
	 * set the backbones transformula.
	 * 
	 * @param formula
	 */
	public void setFormula(final TransFormula formula) {
		mFormula = formula;
	}

	/**
	 * set the backbones symbolic memory.
	 */
	public void setSymbolicMemory(final SymbolicMemory memory) {
		mSymbolicMemory = memory;
	}

	/**
	 * set the backbones abstract path condition (accelerated backbone)
	 * 
	 * @param condition
	 */
	public void setAbstractPathCondition(final Term condition) {
		mAbstractPathCondition = condition;
	}

	/**
	 * Assign a new nested {@link Loop} tot the backbone
	 * 
	 * @param loopHead
	 *            the loophead {@link IcfgLocation} of the nested loop
	 */
	public void addNestedLoop(final IcfgLocation loopHead) {
		mNestedLoops.add(loopHead);
		mIsNested = true;
	}

	/**
	 * add a new Transition in form of an {@link IcfgEdge} to the backbone.
	 * 
	 * @param transition
	 *            the new transition.
	 */
	public void addTransition(final IcfgEdge transition) {
		mPath.addLast(transition);
		mNodes.addLast(transition.getSource());
	}

	/**
	 * Returns the path of the backbone.
	 *
	 * @return the path of the backbone
	 */
	public Deque<IcfgEdge> getPath() {
		return mPath;
	}

	/**
	 * Returns the nodes in the backbone.
	 * 
	 * @return nodes in the backbone.
	 */
	public Deque<IcfgLocation> getNodes() {
		return mNodes;
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
	public UnmodifiableTransFormula getCondition() {
		return mCondition;
	}

	public List<IcfgLocation> getNestedLoops() {
		return mNestedLoops;
	}

	public SymbolicMemory getSymbolicMemory() {
		return mSymbolicMemory;
	}

	public Term getAbstractPathCondition() {
		return mAbstractPathCondition;
	}

	public Boolean isNested() {
		return mIsNested;
	}

	@Override
	public String toString() {
		final StringBuilder b = new StringBuilder();
		b.append(" { ");
		for (final IcfgLocation node : mNodes) {
			b.append(node + " -> ");
		}
		b.append(mPath.getLast().getTarget() + " } ");
		return b.toString();
	}

}
