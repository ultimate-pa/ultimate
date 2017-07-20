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

import java.util.Deque;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Term;
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
	private final List<Loop> mNestedLoops;
	private TermVariable mPathCounter;
	private Term mCondition;
	private SymbolicMemory mSymbolicMemory;

	/**
	 * Construct a new backbone for a loop
	 *
	 * @param path
	 *            The path of the backbone in the {@link IIcfg}.
	 * @param tf
	 *            The paths {@link TransFormula}.
	 * 
	 * @param nestedLoops
	 *            Nested loops in the backbone
	 */
	public Backbone(final Deque<IcfgEdge> path, final TransFormula tf, final List<Loop> nestedLoops) {
		mPath = path;
		mFormula = tf;
		mPathCounter = null;
		mCondition = null;
		mSymbolicMemory = null;
		mNestedLoops = nestedLoops;
	}

	public void setPathCounter(final TermVariable pathCounter) {
		mPathCounter = pathCounter;
	}

	/**
	 * set the backbone's entry condition.
	 *
	 * @param condition
	 *            the backbone's condition.
	 */
	public void setCondition(final Term condition) {
		mCondition = condition;
	}

	public void setSymbolicMemory(final SymbolicMemory memory) {
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
	public Term getCondition() {
		return mCondition;
	}

	public List<Loop> getNestedLoops() {
		return mNestedLoops;
	}

	public SymbolicMemory getSymbolicMemory() {
		return mSymbolicMemory;
	}

	@Override
	public String toString() {
		return mPath.toString();
	}

}
