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
	private List<TermVariable> mAuxVars;

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
		mAuxVars = new ArrayList<>();
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

	public List<TermVariable> getVars() {
		return mAuxVars;
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
	
	/**
	 * add a var
	 * @param vars
	 */
	public void addVar(List<TermVariable> vars) {
		mAuxVars.addAll(vars);
	}

	@Override
	public String toString() {
		return mPath.toString();
	}

	/**
	 * Get the {@link Backbone}s as human readable Text.
	 * 
	 * @return
	 */
	public String backbonesToString() {
		StringBuilder str = new StringBuilder();
		for (Backbone backbone : mBackbones) {
			str.append(backbone.toString());
		}
		return str.toString();
	}

}
