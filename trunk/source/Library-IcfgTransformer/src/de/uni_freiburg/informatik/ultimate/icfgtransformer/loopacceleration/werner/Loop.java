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
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * A Loop
 *
 * @author Jonas Werner (jonaswerner95@gmail.com)
 */

public class Loop {

	private final IcfgLocation mLoopHead;
	private final ManagedScript mScript;
	private Term mCondition;
	private Deque<IcfgEdge> mPath;
	private Deque<Backbone> mBackbones;
	private IteratedSymbolicMemory mIteratedMemory;
	private List<TermVariable> mAuxVars;
	private Map<IcfgLocation, Backbone> mErrorPaths;
	private Boolean mHasNestedLoops;
	private Deque<Loop> mNestedLoops;
	private Boolean mIsSummarized;
	private Map<IProgramVar, TermVariable> mInVars;
	private Map<IProgramVar, TermVariable> mOutVars;
	private IcfgLocation mLoopExit;
	private List<IcfgEdge> mExitTransitions;
	private List<IcfgEdge> mEntryTransitions;
	private List<UnmodifiableTransFormula> mExitConditions;
	private UnmodifiableTransFormula mFormula;

	/**
	 * Construct a new loop.
	 * 
	 * @param loopHead
	 *            The loop entry node.
	 */
	public Loop(final IcfgLocation loopHead, final ManagedScript script) {
		mPath = null;
		mLoopHead = loopHead;
		mScript = script;
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
		mLoopExit = null;
		mExitConditions = new ArrayList<>();
		mExitTransitions = new ArrayList<>();
		mEntryTransitions = new ArrayList<>();

		mFormula = null;
	}

	/**
	 * unify the vars
	 * 
	 * @param tf
	 * @param inVars
	 * @param outVars
	 * @return Transformula with unified var names
	 */
	public TransFormula updateVars(final TransFormula tf, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars) {
		if (SmtUtils.isFalse(tf.getFormula())) {
			return tf;
		}

		final Map<IProgramVar, TermVariable> newInVars = new HashMap<>(inVars);
		final Map<IProgramVar, TermVariable> newOutVars = new HashMap<>(outVars);

		final Map<Term, Term> subMapping = new HashMap<>();

		for (final Entry<IProgramVar, TermVariable> oldVar : tf.getInVars().entrySet()) {
			if (!inVars.containsKey(oldVar.getKey())) {
				newInVars.put(oldVar.getKey(), oldVar.getValue());
				subMapping.put(oldVar.getValue(), oldVar.getValue());
			} else {
				newInVars.put(oldVar.getKey(), inVars.get(oldVar.getKey()));
				subMapping.put(oldVar.getValue(), inVars.get(oldVar.getKey()));
			}
		}
		for (final Entry<IProgramVar, TermVariable> oldVar : tf.getOutVars().entrySet()) {
			if (!outVars.containsKey(oldVar.getKey())) {
				newOutVars.put(oldVar.getKey(), oldVar.getValue());
				subMapping.put(oldVar.getValue(), oldVar.getValue());
			} else {
				newOutVars.put(oldVar.getKey(), outVars.get(oldVar.getKey()));
				subMapping.put(oldVar.getValue(), outVars.get(oldVar.getKey()));
			}
		}

		final Substitution sub = new Substitution(mScript, subMapping);
		final Term updatedTerm = sub.transform(tf.getFormula());
		final TransFormulaBuilder tfb = new TransFormulaBuilder(newInVars, newOutVars, true, null, true, null, true);
		tfb.setFormula(updatedTerm);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(mScript);
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

	public UnmodifiableTransFormula getFormula() {
		return mFormula;
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

	public IcfgLocation getLoopExit() {
		return mLoopExit;
	}

	public List<UnmodifiableTransFormula> getExitConditions() {
		return mExitConditions;
	}

	public List<IcfgEdge> getEntryTransitions() {
		return mEntryTransitions;
	}

	public List<IcfgEdge> getExitTransitions() {
		return mExitTransitions;
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

	public void setPath(final Deque<IcfgEdge> path) {
		mPath = path;
		for (final IcfgEdge entry : mLoopHead.getOutgoingEdges()) {
			if (mPath.contains(entry)) {
				mEntryTransitions.add(entry);
			}
		}
	}

	public void setLoopExit(final IcfgLocation icfgLocation) {
		mLoopExit = icfgLocation;
		for (final IcfgEdge trans : icfgLocation.getIncomingEdges()) {
			final IcfgLocation source = trans.getSource();
			for (final IcfgEdge out : source.getOutgoingEdges()) {
				if (mPath.contains(out)) {
					mExitTransitions.add(trans);
					break;
				}
			}

		}
	}

	public void addExitCondition(final UnmodifiableTransFormula exitCondition) {
		mExitConditions.add(exitCondition);
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

	public void replaceErrorPath(final IcfgLocation errorLocation, final Backbone newErrorPath) {
		mErrorPaths.replace(errorLocation, newErrorPath);
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

	public void setFormula(final UnmodifiableTransFormula tf) {
		mFormula = tf;
	}

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
